#!/usr/bin/env python
"""
TODO : 
- Verify date. This is particularly important for nmmb since the file name does not have the 
  date and using the wrong date will result in obscure errors
- Deal gracefully with errors thrown by subprocess commands
   e.g. qsub - what if the job could not be submitted due to limit
   -> CalledProcessError:
- wgrib2 -new_grid will save interpolation weights, so it may be worth performing
  the interpolation on combined grid data if possible (if using simultaneous_mode 
  and/or one-field-per-fieldset
- Locking seems to be buggy - should we use Lock from multiprocessing instead of produtil?  
  -> produtil uses fcntl to lock files, so it's not just thread safe
- optimize run time estimates
- Commented out part that skips existing files (since it is not robust enough)
: Database is only updated in simultaneous_mode 
- regrid_output (to latlon) runs on the frontend (only takes like 3 minutes max)
- debug_mode still deletes the temp dir
NOTES
- Changes in params.conf between runs with the same "database" can cause problems.
  e.g. if you change process_fields_individually, since that will cause the
  list of `fieldset's to be different (see get_fieldsets())
"""
import os
import time
from datetime import datetime as dtime
from datetime import timedelta as tdelta
from ConfigParser import ConfigParser, NoSectionError
from optparse import OptionParser
import sys
import copy
import subprocess 
from subprocess import CalledProcessError
import xml.dom.minidom
import xml.etree.ElementTree as ET
import shutil
import logging
from distutils.util import strtobool
#import threading
import multiprocessing as mp
import pickle
import collections

import produtil
from produtil.cd import TempDir
from produtil.run import mpirun, mpi, openmp, checkrun, bigexe
#
# Set constants
#
GRID_NUMBER = "4" # this is before latlon conversion
ORIG_CENTER = "nws_ncep"
SUB_CENTER = "ncep_nco"
VERSION_NO = "v2003"
LOCAL_TABLE_VERSION = "local_tab_yes1"
SIG_REF_TIME = "fcst"
PROD_STATUS = "oper"
DATA_TYPE = "fcst"
GEN_PROC_TYPE = "fcst"
PACKING_METHOD = "complex_packing_spatial_diff"
ORDER_OF_SPTDIFF = "2nd_ord_sptdiff"
FIELD_DATATYPE = "fltng_pnt"
COMPRESSION = "lossless"
OUTPUT_FORMAT = "grib2" # no support for grib1, at least for now
JOB_POLL_INTERVAL = 30
upp_version = "3.1"
template_dir = os.path.join("/home/Javier.Delgado/scripts/run_upp/stable", "upp_template_dir", upp_version)
# TODO : This should be in config
#UPP_HOME = "/home/Javier.Delgado/apps/upp/dtc/3.1/vanilla" # FAILING
UPP_HOME = "/home/Javier.Delgado/apps/upp/dtc/" + upp_version + "/nr"
WGRIB2_EXE = "/apps/wgrib2/0.1.9.5.1/bin/wgrib2"
KEEP_TEMP_DIRECTORY = True # TODO - have debug option
INTERPOLATE_TO_LATLON = True
MAX_JOBS = 140 # setting too high may be waht causes random failures
db_file = 'succeeded_fieldsets.pickle'

class InputSource(object):
    """
    Encapsulate attributes of a UPP input source. This class should not
    be used. Use one of the subclasses that are specific to an input
    source.
    """
    def __init__(self, initDate, modelDir, infilePattern):
        """ Initialization date of the forecast """
        self.init_date = initDate
        """Path to history files"""
        self.model_dir = modelDir
        """Pattern of history files"""
        self.infilePattern = infilePattern

    def create_itag(self, fcstOffset, domainNum=1):
        """ Domain/grid number for nested runs """
        
        fhr = int(fcstOffset.total_seconds() / 3600)
        fcst_min = int(fcstOffset.total_seconds() % 3600 / 60)
        fcst_date = self.init_date + fcstOffset
        conversion_args = {"domNum":domainNum, "fhr":fhr, "fmin":fcst_min,
                           "fdate":fcst_date, "init_date":self.init_date}
        infile = self.infilePattern.format(**conversion_args)
        infile = os.path.join(self.model_dir, infile)
        itag = open("itag", "w")
        itag.write("{infile}\n".format(infile=infile)) # TODO : full path?
        itag.write("{0}\n".format(self.data_format))
        itag.write("{0}\n".format(OUTPUT_FORMAT))
        itag.write("{0:%Y-%m-%d_%H:%M:00}\n".format(fcst_date))
        itag.write("{0}\n".format(self.tag))
        itag.close()

class NMMBInputSource(InputSource):
#fout_d${dom_id}_${YY}-${MM}-${DD}_${HH}:00:00
#nmmb_hst_${dom_id}_nio_${fhr4}h_00m_00.00s
    def __init__(self, initDate, modelDir,
            infilePattern="nmmb_hst_{domNum:02d}_nio_{fhr:04d}h_{fmin:02d}m_00.00s"):
        super(NMMBInputSource, self).__init__(initDate, modelDir, 
                                              infilePattern)
        self.dataset_type_str = "NMBPRS"
        self.gen_proc_str = "nmmb"
        #self.gen_proc_str = "wrf_em_ncar_arwrf"
        self.data_format = "binarynemsio"
        self.dyncore = "NMB"
        self.tag = "NMM"
        self.modelstr = "nmb" # used for prefix

    def unipost_outfile_name(self, fcstOffset):
        fhr = int(fcstOffset.total_seconds() / 3600)
        fmin = int(fcstOffset.total_seconds() % 3600 / 60)
        #return "NMBPRS{fhr:2d}.tm00"
        if fmin == 0: 
            return "NMBPRS.GrbF{fhr:02d}".format(fhr=fhr, fmin=fmin)
        else: 
            # For my modified version of unipost.exe, which puts the 3-digit fhr
            #return "NMBPRS.GrbF{fhr:02d}.{fmin:02d}".format(fhr=fhr, fmin=fmin)
            return "NMBPRS.GrbF{fhr:03d}.{fmin:02d}".format(fhr=fhr, fmin=fmin)
    
    def domain_details_file(self, domainNum):
        # TODO : can't we use configure_file instead?
        fil = "domain_details_{dom:02d}".format(dom=domainNum)
        return os.path.join(self.model_dir, fil)
    
    def extents(self, domainNum=1):
        """@return southLat, northLat, westLon, eastLon"""
        # TODO : Do this for NMM - we can probably reuse latlon_corners
        ret = [None, None, None, None]
        #import pdb ; pdb.set_trace()
        # This is what it produced (which failed):
        #'['/apps/wgrib2/0.1.9.5.1/bin/wgrib2', 'NMBPRS.GrbF00', '-new_grid', 'latlon', '-15817707.8:800:0.027', '2296727.5:800:0.027', 'nmbprs.grbf00']' returned non-zero exit status 8
        # 13780365   259088562   13780365   -79088539   35270081  -103013275   35270081   283013275
        #
        # SW lat,lon:   13.780  -100.911                              
        #NE lat,lon:   35.270   -76.987

        if os.path.exists("latlons_corners.txt"):
            #     -18088     -100328     -18088      -19672      49000     -129665      49000     -350335

            log.debug("Using latlon_corners.txt to get grid extents")
            with open("latlons_corners.txt") as f:
                toks = f.readlines()[0].split()
                # order in file: LATSTART,LONSTART,LATSE,LONSE,LATNW,LONNW,
               # Note: I'm using the lat/lonStart and lat/lonEnd as opposed to the SE and NW 
               #       values. This will result in many missing values on the west side due to
               #       the conversion to Lat-Lon from whatever the model uses. Since copygb_hwrf.txt
               #       generated for NMM-E/HWRF grids uses the start and end values, I'll go with
               #       the same convention here, although there seems to be less missing points for those.
                #ret = [float(toks[i]) for i in (2,4,3,5)]
                #ret = [float(toks[i]) for i in (1,7,2,8)]
                ret = [float(toks[i]) for i in (0,6,5,7)]
                #ret[0] /= 10**6. ; ret[1] /= 10**6. ; ret[2] /= 10**5. ; ret[3] /= 10**5.
                # UPDATE : Did this change for version 3.1 or is something else happening?
                #     TODO : Check if it's version dependent (i.e. e6 vs e3)
                #ret[0] /= 10**6. ; ret[1] /= 10**6. ; ret[2] /= 10**6. ; ret[3] /= 10**6.   <-- was working for 3.0
                ret[0] /= 10**3. ; ret[1] /= 10**3. ; ret[2] /= 10**3. ; ret[3] /= 10**3.
        elif os.path.exists(self.domain_details_file(domainNum)):
            with open(self.domain_details_file(domainNum)) as f:
                lines = f.readlines()
                log.debug("Using domain_details file to get grid size")
                for line in lines:
                     if line.startswith("SW lat,lon"):
                        toks = line.split()
                        ret[0] = float(toks[2])
                        ret[2] = float(toks[3])
                     elif line.startswith("NE lat,lon"):
                         ret[1] = float(toks[2])
                         ret[3] = float(toks[3])
        assert not None in ret
        return ret
             
    def resolution(self, domainNum=1):
        if os.path.exists("copygb_gridnav.txt"):
            log.debug("Using copygb_gridnav output to get resolution")
            dat = open("copygb_gridnav.txt").readlines()[0].split()
            dx = float(dat[8])
            dy = float(dat[9])
            # unipost puts value in millidegress for grib2
            #dx /= 1.e6 # UPDATE : for 3.1? TODO
            dx /= 1.e3
            #dy /= 1.e6 # UPDATE : For 3.1? TODO
            dy /= 1.e3
            # since it's LCC, dx is multiplied by 107 and dy 110
            dx /= 107.
            dy /= 110.
        else:
            log.debug("Using domain_details for resolution")
            lines = open(self.domain_details_file(domainNum)).readlines()
            for line in lines:
                if line.startswith("dlmd"):
                    dx = float(line.split()[1])
                elif line.startswith("dphd"):
                    dy  = float(line.split()[1])
        return (dx,dy)
                
    def gridsize(self, domainNum=1):
        if os.path.exists("copygb_gridnav.txt"):
            log.debug("Using copygb_gridnav output to get grid size")
            dat = open("copygb_gridnav.txt").readlines()[0].split()
            nx = int(dat[2])
            ny = int(dat[3])
        elif os.path.exists(self.domain_details_file(domainNum)):
            log.debug("Using domain_details file to get grid size")
            lines = open(self.domain_details_file(domainNum)).readlines()
            for line in lines:
                if line.startswith("nx"):
                    nx = int(line.split()[1])
                elif line.startswith("ny"):
                    ny = int(line.split()[1])
        else:
            raise Exception("Unable to get grid size()")
        return (nx,ny)
            
class WRFNMMInputSource(InputSource):
    def __init__(self, initDate, modelDir, dataFormat="netcdf",
             infilePattern="wrfout_d{domNum:02d}_{fdate:%Y-%m-%d_%H:%M:00)"):
        assert dataFormat in ("netcdf", "binary", "binarympiio")
        # TODO FILL OUT THE REST
        self.data_format = dataFormat
        self.modelstr = "wrf"

class Fieldset(object):
    """ This class has no specific functionality. It is just a convenience
        class to encapsulate fieldset parameters"""
    def __init__(self):
        self.pnames = [] ; self.shortnames = [] ; self.table_infos = [] 
        self.scales = []
    def __repr__(self):
        s = "shortnames: {0}\npnames: {1}\nscales: {2}\ntable_infos: {3}"\
            .format(`self.shortnames`, `self.pnames`, `self.scales`, 
                    `self.table_infos`)
        if hasattr(self, "levels"):
            s += '\nlevels: {0}'.format(`self.levels`)
        return s

def _default_log(log2stdout=logging.INFO, log2file=None, name='el_default'):
    global _logger
    if _logger is None:
        _logger = logging.getLogger(name)
        _logger.setLevel(log2stdout)
        msg_str = '%(asctime)s::%(name)s::%(lineno)s::%(levelname)s - %(message)s'
        msg_str = '%(asctime)s::%(funcName)s::%(filename)s:%(lineno)s::%(levelname)s - %(message)s'
        date_format = "%H:%M:%S"
        formatter = logging.Formatter(msg_str, datefmt=date_format)
        if log2file is not None:
            fh = logging.FileHandler('log.txt')
            fh.setLevel(log2file)
            fh.setFormatter(formatter)
            _logger.addHandler(fh)
        if log2stdout is not None:
            ch = logging.StreamHandler()
            ch.setLevel(log2stdout)
            ch.setFormatter(formatter)
            _logger.addHandler(ch)
    return _logger
_logger=None

def _parse_args():
    global g_debug_mode
    #import pdb ;pdb.set_trace()
    usage="usage: %prog [options] <database file> <config file1 [config_file2 ...]> "\
          "[config_fileN ... config_fileN+M] [input_file1,...input_fileN]"\
          "".format() + __doc__
    parser = OptionParser(usage=usage)
    #parser.add_option("-f", "--file", dest="input_file", optional=False)
    #parser.add_option("-c", "--config", dest="config_file")
    parser.add_option("-d", "--debug_mode", dest="debug_mode", 
                      action="store_true", default=False,
                      help="Enables debug mode - Retains all temporary "\
                           "directories and sets loggin to DEBUG (overridable "\
                           "with --log-level)")
    parser.add_option("-l", "--log-level", dest="log_level", default=logging.INFO,
                      help="(0-100 or constant defined in the logging module")
    parser.add_option("-o", "--conf-override", dest="conf_overrides",
                      action="append", 
                      help="Override config setting (section.item=value)")
    (options, args) = parser.parse_args()
    if len(args) < 2:
        print usage
        sys.exit(1)
    
    db_file = args[0]
    config_files = args[1:]

    # Warn user if there are non-existant config files
    if len(config_files) > 1:
        for cf in config_files[1:]:
            if not os.path.exists(cf):
                print("WARN :: Specified config file '{0}' does not exist".format(cf))
                #log.warn("Specified config file '{0}' does not exist".format(cf))

    if options.debug_mode:
        g_debug_mode = True
        log_level = logging.DEBUG

    try:
        log_level = int(options.log_level)
    except ValueError:
        try:
            log_level = getattr(logging, options.log_level)
        except:
            print 'Unrecognized log level:', options.log_level, '. Not setting.'
    conf_overrides = options.conf_overrides if options.conf_overrides else []
    return (db_file, config_files, log_level, conf_overrides)

def guess_model_type(modelDir):
    if os.path.exists(os.path.join(modelDir, "namelist.input")):
        if os.path.exists(os.path.join(modelDir, "real_nmm.exe")):
            log.debug("Guessing this is a WRF-NMM run")
            return "nmm"
        elif os.path.exists(os.path.join(modelDir, "real.exe")):
            log.debug("Guessing this is a WRF-ARW run")
            return "arw"
        else:
            raise Exception("Unable to guess run type")
    elif os.path.exists(os.path.join(modelDir, "configure_file_01")):
         log.debug("Guessing this is an NMM-B run")
         return "nmmb"
    else:
         raise Exception("Unable to guess run type in model dir: {0}"
                         .format(modelDir))
     
def datestr_to_datetime(startDate):
    """  
    Convert a string in `MM-DD-YYYY hh:mm' format to a datetime
    @param startDate The String
    @return the datetime object
    """
    try: 
        mdy = startDate.split(" ")[0]
        hm = startDate.split(" ")[1]
        (month, day, year) = [int(x) for x in mdy.split("-")]
        (hour, minute) = [int(x) for x in hm.split(":")]
        #startDate = startDate.replace("'", "").replace('"', '')
        #os.environ['TZ'] = 'UTC'
        #tzset()
        #return time.mktime(time.strptime(startDate, '%m-%d-%Y %H:%M'))
        return dtime(year=year, month=month, day=day,
                                 hour=hour, minute=minute)
    except ValueError:
        print 'Given start date', startDate, 'does not match expected format MM-DD-YYYY hh:mm'
        sys.exit(1)

def add_basic_nodes(paramset, insrc, timeRangeUnit="hour"):
    dataset = ET.SubElement(paramset, "datset") # note its datset, not dataset
    dataset.text = insrc.dataset_type_str

    grid_num = ET.SubElement(paramset, "grid_num")
    grid_num.text = GRID_NUMBER

    sub_center = ET.SubElement(paramset, "sub_center")
    sub_center.text = SUB_CENTER

    version_no = ET.SubElement(paramset, "version_no")
    version_no.text = VERSION_NO

    local_table_vers_no = ET.SubElement(paramset, "local_table_vers_no")
    local_table_vers_no.text = LOCAL_TABLE_VERSION 

    sigreftime = ET.SubElement(paramset, "sigreftime")
    sigreftime.text = SIG_REF_TIME 

    prod_status = ET.SubElement(paramset, "prod_status")
    prod_status.text = PROD_STATUS 

    data_type = ET.SubElement(paramset, "data_type")
    data_type.text = DATA_TYPE

    gen_proc_type = ET.SubElement(paramset, "gen_proc_type")
    gen_proc_type.text = GEN_PROC_TYPE

    time_range_unit = ET.SubElement(paramset, "time_range_unit")
    time_range_unit.text = timeRangeUnit

    orig_center = ET.SubElement(paramset, "orig_center")
    orig_center.text = ORIG_CENTER

    gen_proc = ET.SubElement(paramset, "gen_proc")
    gen_proc.text = insrc.gen_proc_str

    packing_method = ET.SubElement(paramset, "packing_method")
    packing_method.text = PACKING_METHOD

    order_of_sptdiff = ET.SubElement(paramset, "order_of_sptdiff")
    order_of_sptdiff.text = ORDER_OF_SPTDIFF

    field_datatype = ET.SubElement(paramset, "field_datatype")
    field_datatype.text = FIELD_DATATYPE

    comprs_type = ET.SubElement(paramset, "comprs_type")
    comprs_type.text = COMPRESSION

def ___get_list_of_dates(start_date, duration, interval):
    dateRange = range(0, duration+1, frequency)
    all_dates = [startDate + tdelta(seconds=curr) for curr in dateRange]
    fhr = tdelta(hours=firstFhr)
    for currDate in all_dates:
        
         fhr += interval

def create_xml_parm_file(insrc, fieldset, filename="postcntrl.xml"):
    # general
    xmlFile = open(filename, "w")
    root = ET.Element('postxml')
    paramset = ET.SubElement(root, "paramset")
    #insrc = NMMBInputSource()
    add_basic_nodes(paramset, insrc)
    #import pdb ; pdb.set_trace()

    # run-specific (i.e. <param> nodes)
    #add_field_node(fieldset, insrc)
    # KIM: levels attr is shared by all fields in fieldset
    for pname, shortname, scale, table_info in \
       zip(fieldset.pnames, fieldset.shortnames, fieldset.scales, 
           fieldset.table_infos):
       param_node = ET.SubElement(paramset, "param")
       sn_node = ET.SubElement(param_node, "shortname")
       sn_node.text = shortname
       pname_node = ET.SubElement(param_node, "pname")
       pname_node.text = pname
       # scalar fields have no level node
       # (v) UPP produces nothing if lev values have trailing 0; e.g. 1.0 instead of 1.
       #level_node.text = ''.join(str(l)+" " for l in fieldset.levels)
       if hasattr(fieldset, "levels"):
         level_node = ET.SubElement(param_node, "level")
         level_node.text = ''.join(str(l).replace(".0",".")+" " for l in fieldset.levels)
       scale_node = ET.SubElement(param_node, "scale")
       scale_node.text = str(scale)
       if table_info is not None:
           ti_node = ET.SubElement(param_node, "table_info")
           ti_node.text = table_info

    # general
    xmlOut = xml.dom.minidom.parseString(ET.tostring(root))
    # UPP will silently and annoyingly FAIL if using tabs instead of spaces
    # Not a problem with newer versions that use the text file instead
    xmlText = xmlOut.toprettyxml(indent="   ") 
    # hack to replace generated &amp;
    for line in xmlText.splitlines():
        #import pdb ; pdb.set_trace()
        # the UPP XML parser seems to ignore characters after 200 or so, 
        # at least with the <level> node. Use threshold of 150 to be safe
        # TODO move this outside to a recursive function
        if len(line) > 150:
            assert len(line) < 350 # since we only do it once (see above comment)
            i = 150
            c = line[i]
            while line[i] != " ":
                i -= 1
            l1 = line[:i]
            l2 = line[i:]
            line = l1 + "\n" + l2
        line = line.replace('&amp;', '&')
        xmlFile.write(line + '\n')
    xmlFile.close()

def create_template_dir():
    # create links:
        # exe's
        # fort.14
        # crtm:(lines 257-316)
    raise Exception("TODO")

def process_fieldset_conf(fieldset):
    """
    Get parameters that are specified one-per-field in the config file, 
    i.e. pnames, shortnames, scale, and table_info settings
    """
    if "fields"  in fieldset:
        try:
            suffix = fieldset["_suffix"]
        except KeyError:
            raise Exception("Must specify '_suffix' if specifying fields")
        pnames = [x.strip() for x in fieldset["fields"].split(",")]
        shortnames = [x + suffix for x in pnames]
    elif "field_pnames" in fieldset:
        pnames = [f.strip() for f in fieldset["field_pnames"].split(",")]
        try:
            shortnames = fieldset["field_shortnames"].split(",")
            shortnames = [n.strip() for n in shortnames]
        except KeyError:
                raise Exception("Must specify 'field_shortnames' if "
                                "specifiying pnames".format())
    else:
        raise Exception("Must specify either 'fields' and 'suffix' "
                        "or 'field_shortnames' and 'field_pnames'"
                        .format())
    scales = [float(x) for x in fieldset["scale"].split(",")]
    
    table_infos = [None for i in range(len(scales))]
    if "table_info" in fieldset:
        for i,tableInfo in enumerate(fieldset["table_info"].split(",")):
            if tableInfo.strip() != "-":
                table_infos[i] = tableInfo
        log.debug(table_infos)
    #import pdb ; pdb.set_trace()
    assert len(table_infos) == len(scales) == len(shortnames) == len(pnames)
    return (pnames, shortnames, scales, table_infos)
    
def get_fieldsets(conf, insrc, init_date):
    """ 
    Get a list of ``fieldsets'' which are groups of one or more field
    names and associated parameters from the config
    """
    fieldsets = []
    fs_list = [x.strip() for x in conf.get("BASIC", "fieldsets").split(",")]
    for fsName in fs_list:
        log.debug("Processing config for fieldset '{0}'".format(fsName))
        fs_config = dict(conf.items(fsName + "_fieldset_settings"))
        (pnames, shortnames, scales, table_infos) = process_fieldset_conf(fs_config)
        #import pdb ; pdb.set_trace()
        currFieldset = Fieldset()
        if "levels" in fs_config:
            levels = fs_config["levels"]
            if levels.strip().endswith(","): levels = levels[:-1]
            levels = [float(l) for l in levels.split(",")]
            setattr(currFieldset, "levels", levels)
        output_subpath = fs_config["outfile"].replace("/",os.sep)
        setattr(currFieldset,"outfile_pattern", output_subpath)
        #if strtobool(fs_config["do_fieldsets_simultaneously"]
        

        # NEW
        #setattr(currFieldset, "pnames", pnames)
        #setattr(currFieldset, "shortnames", shortnames)
        #setattr(currFieldset, "scales", scales)
        #setattr(currFieldset, "table_infos", table_infos)
        currFieldset.pnames = pnames
        currFieldset.shortnames = shortnames
        currFieldset.scales = scales
        currFieldset.table_infos = table_infos 

        try:
            fields_per_unipost_job = int(fs_config["fields_per_unipost_job"])
            log.debug("Since 'fields_per_unipost_job' was specified, will "
                      "create subsets of fieldsets".format())
        except KeyError:
            fields_per_unipost_job = len(pnames)
        i = 0
        while i < len(currFieldset.pnames):
            curr_fieldset_subset = Fieldset()
            curr_fieldset_subset.outfile_pattern = currFieldset.outfile_pattern
            if hasattr(currFieldset, "levels"):
                curr_fieldset_subset.levels = currFieldset.levels
            while len(curr_fieldset_subset.pnames) < fields_per_unipost_job\
                  and i < len(currFieldset.pnames):
                #import pdb ; pdb.set_trace()
                for attr in ["pnames", "shortnames", "table_infos", "scales"]:
                    v = getattr(currFieldset, attr)[i]
                    getattr(curr_fieldset_subset, attr).append(v)
                i += 1
            #import pdb ; pdb.set_trace()
            log.info("Adding the following fieldset: {0}".format(curr_fieldset_subset))
            fieldsets.append(curr_fieldset_subset)
        """    
        if strtobool(fs_config["process_fields_individually"]):
            log.debug("'process_fields_individually' set, so each field will be in a fieldset")
            for (pname, shortname, scale, table_info) in \
                           zip(pnames, shortnames, scales, table_infos):
                fs = copy.copy(currFieldset)
                setattr(fs, "pnames", [pname])
                setattr(fs, "shortnames", [shortname])
                setattr(fs, "scales", [scale])
                setattr(fs, "table_infos", [table_info])
                #setattr(fs, "outfile", outfile)
                #conversion_args.update({"fieldShortName":shortname})
                fieldsets.append(fs)
        else:
            setattr(currFieldset, "pnames", pnames)
            setattr(currFieldset, "shortnames", shortnames)
            setattr(currFieldset, "scales", scales)
            setattr(currFieldset, "table_infos", table_infos)
            #conversion_args.update({"fieldShortName":"multifield"})
            fieldsets.append(currFieldset)
    """
    return fieldsets
    
def run_unipost(insrc, fieldset, conf, fcstOffset, jobname):
    """
    Run unipost.exe and monitor its execution
    preC: we are in the working path, all files have been linked, 
          itag has been created, parm file has been created
    """
    # Just use job template for now
    run_as_job = strtobool(conf.get("BASIC", "run_as_job"))
    hpc = dict(conf.items("hpc"))
    if run_as_job:
        walltime = int(float(hpc["walltime_per_fieldset"]) * 3600.)
        #print "jdd", walltime, fieldset.pnames
        # TODO: change to walltime_per_field_level
        #       remember to account for simultaneous_mode and fields/file
        #walltime *= len(fieldset.pnames) 
        #print "jde", walltime
        # NOTE: The increase in runtime for each level is waaay less than linear
        # case in point, with 800x800 domain, it took like 30 seconds for a 
        # surface field and 65 seconds for 3 45-level isobaric fields
        # TODO : Optimize
        #if hasattr(fieldset, "levels"): walltime *= len(fieldset.levels) 
        #if hasattr(fieldset, "levels"): print "jdf", fieldset.levels, len(fieldset.levels)
        #print "jdf", walltime
        # UPDATE : Noticed #fields and #levels don't affect runtime
        walltime += 300 # account for set up, staging, etc.
        args = ["qsub", "-A", hpc["account"], 
            "-lwalltime={0:d}".format(walltime), 
            "-lnodes={0}:ppn={1}".format(hpc["nodes"],hpc["procs_per_node"]),
            "-q", hpc["queue"],
            "-d", ".", "-j", "oe",
            "-N", jobname, "-o", "output.txt",
            "job.zsh"]
        # Submit job, if submission fails (e.g. due to too many jobs in queue, 
        # retry a few times.
        # Note that this will retry regardless of the actuall error
        # (e.g. if asking for the wrong account or for more resources than
        #  allowed)
        # TODO set this as config/global opt
        num_tries = 100
        for i in range(num_tries):
            try:
                subprocess.check_call(args)
                break # if qsub succeeds, no need to iterate
            except CalledProcessError:
                log.info("Unable to submit job. Will retry {0} more times, "
                         "every {1} seconds".format(num_tries-i, JOB_POLL_INTERVAL))
                if i == num_tries:
                    raise Exception("Unable to submit job. Giving up")
                time.sleep(JOB_POLL_INTERVAL)

        job_done = False
        while True:
            #import pdb ; pdb.set_trace()
            time.sleep(JOB_POLL_INTERVAL)
            if os.path.exists("output.txt"):
                f = open("output.txt")
                # line with exit code should be towards end, so read from the end
                for line in f.readlines()[-1:-300:-1]:
                    if "finished for user" in line:
                        job_done = True
                        stat = int(line.split()[-1])
                        success = True if stat == 0 else False
                        log.debug("Job done. Exit status = {0}".format(stat))
                        break 
                if job_done:
                    #import pdb ; pdb.set_trace()
                    break
                else:
                    log.debug("Job still running")
            else:
                log.debug("Job still queued. Sleeping")
        if not success:
            raise Exception("UPP failed in directory {0}".format(os.getcwd()))
    else:
        #import pdb ; pdb.set_trace()
        upp_exe = os.path.join(UPP_HOME, "bin", "unipost.exe")
        cmd = (mpirun(mpi(upp_exe, allranks=True)))
        cmd = cmd > 'jza_out'
        checkrun(cmd, sleeptime=60.)
    # Still gotta make sure GriB 2 files were produced
    log.info("unipost.exe exited successfully. Checking output")
    #duration = int(float(conf.get("BASIC", "duration")) * 3600.)
    #interval = int(float(conf.get("BASIC", "interval")) * 3600.)
    ## TODO : Assuming we start at 00
    #for i in range(0, duration+1, interval):
    tmp_outfile  = insrc.unipost_outfile_name(fcstOffset)
    currFile = tmp_outfile
    wgrib_cmd = [WGRIB2_EXE, currFile]
    p = subprocess.check_call(wgrib_cmd) # ensure no errors first
    p = subprocess.Popen(wgrib_cmd, stdout=subprocess.PIPE)
    output = p.communicate()[0].strip()    
    num_gribs = output.count("\n") + 1
    if hasattr(fieldset, "levels"):
        numLevs =   len(fieldset.levels)
    else: # 2d
        numLevs = 1
    expected = len(fieldset.pnames) * numLevs
    if expected != num_gribs:
        raise Exception("Found {0} grib entries in '{1}' but expected {2}; "
                        "expected = num_field * num_levels ({3} * {4})"
                        .format(num_gribs, tmp_outfile, expected, 
                                len(fieldset.pnames), numLevs))

def cat_file(src, dest):
    """
    Move a file from src path to dest path. If dest path exists, concatenate
    it. This is a thread-safe operation, although it uses a rudimentary 
    locking mechanism.
    """
    lock_file = os.path.join(os.path.dirname(dest), 
                             ".lock_" + os.path.basename(dest))
    with produtil.locking.LockFile(filename=lock_file, logger=log, max_tries=10) as lock:    
        if os.path.exists(dest):
            log.info("Destination file '{0}' exists. Will concatenate to it"
                     .format(dest))
            srcObj = open(src, "rb")
            destObj = open(dest, 'ab')
            shutil.copyfileobj(srcObj, destObj, 65536) # last arg=buff size
            srcObj.close()
            destObj.close()       
        else:
            log.debug("Moving file {0}->{1}".format(src, dest))
            shutil.move(src, dest)
    if not os.path.exists(lock_file):
        log.warn("jza33 lock file {0} does not exist!".format(lock_file))
    else:
        os.unlink(lock_file)

def ____cat_file(src, dest):
    """
    Move a file from src path to dest path. If dest path exists, concatenate
    it. This is a thread-safe operation, although it uses a rudimentary 
    locking mechanism.
    """
    lock_file = os.path.join(os.path.dirname(dest), 
                             ".lock_" + os.path.basename(dest))
    while os.path.exists(lock_file):
        log.debug("Lock file {0} exists, sleeping 30".format(lock_file))
        time.sleep(30)
    l = open(lock_file, "w")
    l.close()
    if os.path.exists(dest):
        log.info("Destination file '{0}' exists. Will concatenate to it"
                 .format(dest))
        srcObj = open(src, "rb")
        destObj = open(dest, 'ab')
        shutil.copfileobj(srcObj, destObj, 65536) # last arg=buff size
        srcObj.close()
        destObj.close()       
    else:
        log.debug("Moving file {0}->{1}".format(src, dest))
        shutil.move(src, dest)
    os.unlink(lock_file)

def regrid_output(insrc, infile, outfile, domain, fieldset=None, separate_files=False, conf=None):
    """ Regrid the given grib file to latlon """
    #wgrib2 in.grb -new_grid latlon -135.738:5000:.027 -21.64:2500:.027 jza.grb
    # wgrib2 nmbprs_HGT_2006091000.f000.grb2 -new_grid latlon 224.2:5000:.027 -21.64:2500:.027  jza.grb2
    ##old
    #grid_extents = [str(int(x)) for x in insrc.extents(domainNum=domain)] 
    #(nx,ny) = [str(x) for x in insrc.gridsize(domainNum=domain)]
    ##new
    grid_extents = [int(x) for x in insrc.extents(domainNum=domain)]
    #log.warn("Grid extents: {0}".format(grid_extents))
    #print "grid_extents: ", grid_extents 
    #grid_extents[0] -= 10
    #grid_extents[2] -= 20
    #log.warn("Grid extents: {0}".format(grid_extents))
    #print "grid_extents: ", grid_extents 
    (nx,ny) = insrc.gridsize(domainNum=domain)
    if conf:
        try:
            nxmult = float(conf.get("domain", "nx_multiplication"))
            nymult = float(conf.get("domain", "ny_multiplication"))
            nx = int(nxmult * nx)
            ny = int(nymult * ny)
        except : # NoOptionError
            pass
    ##
    (dx,dy) = insrc.resolution(domainNum=domain)
    latstr = "{0}:{1}:{2}".format(grid_extents[0], str(ny), str(dy))
    lonstr = "{0}:{1}:{2}".format(grid_extents[2], str(nx), str(dx))
    # NOTE: Setting -new_grid_winds to 'grid' to mirror the Table 7 value of 136 used in 
    # copygb
    # hack:  nmmb specific ##replace -multifield- with the pname in case there are multiple 
    # fields per outfile
    # TODO : unhack
    if fieldset is not None and separate_files:
        for pname in fieldset.pnames:
            # UGRD and VGRD must be processed together if regridding
            if pname == "VGRD": continue
            # NOTE : This is the native name. e.g. nmbprs.grbf00
            if pname == "UGRD": 
                pname = "UGRD|VGRD"
                # hack: assuming we want this name
                # TODO : What if user is putting everything in one file?
                outnow = outfile.replace("nmbprs", "nmbprs_winds") 
            else:
                outnow = outfile.replace("nmbprs", "nmbprs_"+ pname)
            inv = subprocess.Popen(["wgrib2", "-s",infile], stdout=subprocess.PIPE)
            subset = subprocess.Popen(["grep", "-E", pname], stdout=subprocess.PIPE, stdin=inv.stdout)
            #new = subprocess.check_output(["wgrib2", infile, "-GRIB", outnow], stdin=subset.stdout)
            subprocess.check_call(["wgrib2", "-i", infile,  "-new_grid_winds", 
                                   "grid", "-new_grid", "latlon", lonstr, latstr, 
                                   # No '-GRIB' if regridding at the same time, 
                                   # only necessary if subsetting only
                                   #"-GRIB", outnow], stdin=subset.stdout) 
                                   outnow], stdin=subset.stdout)
            # Now separate UGRD and VGRD
            #import pdb ; pdb.set_trace()
            if pname == "UGRD|VGRD":
                # NOTE : U and V grids must be adjacent and U must be before V 
                # for new_grid to work!
                for fld in ["UGRD","VGRD"]:
                    log.debug("Subsetting 'winds' to UGRD and VGRD")
                    outnow_fld = outnow.replace("winds", fld)
                    inv = subprocess.Popen(["wgrib2", "-s", outnow], stdout=subprocess.PIPE)
                    subset = subprocess.Popen(["grep", "-E", fld], stdout=subprocess.PIPE, stdin=inv.stdout)
                    subprocess.check_call(["wgrib2", "-i", outnow, "-GRIB", outnow_fld], stdin=subset.stdout)
                #os.unlink(outnow) # TODO uncomment after testing
    else:
        log.debug("Regriding using command: wgrib2 {0} -new_grid_winds grid -new_grid latlon  {1} {2} {3}"
                  .format(infile, lonstr, latstr, outfile))
        cmd = [WGRIB2_EXE, infile, "-new_grid_winds", "grid", "-new_grid", 
               "latlon", lonstr, latstr, outfile]
        subprocess.check_call(cmd)
    # TODO : verify output - see code  at end of run_unipost

def run_upp(fieldset, insrc, domain, init_date, fcst_offset, templateDir, conf,
            outfile, jobname, hack_lock, log2file=False):
    """
    :param fieldset: The Fieldset, which contians fields to process in this UPP run
    :param insrc: InputSource corresponding to native fields 
    :param conf: The ConfigParser object that drives this program
    :param  outfile: The path to the output file: 
            <output_dir>/<fieldset.outfile_pattern>
            If calling from main(), output_dir is the config item [BASIC]output_dir
            fieldset.outfile_pattern is whatever is put in the config section 
            for the outfile
    """            
    #import pdb ; pdb.set_trace()
    # Note: Dir contents will be printed if exception is caught
    pfx = "/home/Javier.Delgado/scratch/upp/upp_workdir_" # TODO : in config or GLOBAL
    # If specified, log individual jobs to separate log (text) files.
    # Just add handler to global log since we're in a separate process.
    # TODO : Since jobname is currently just a function of field's pname,
    #        dom, and date, there will be more than one jobs writing
    #        to the same file (e.g. isobaric TMP and hybrid TMP)
    if log2file:
        # TODO purge old log files
        fh = logging.FileHandler('log/log_{0}.txt'.format(jobname))
        fh.setLevel(log.level)
        # ASSUME : only one handler
        fh.setFormatter(log.handlers[0].formatter)
        log.addHandler(fh)

    with TempDir(prefix=pfx,cd=True, keep_on_error=True, 
                 keep=g_debug_mode, logger=log) as td:
        ##
        #os.mkdir("foo")
        #os.chdir("foo")
        ##
        # Copy template dir; since we copy the whole tree, go into it
        templateDir = templateDir[:-1] if templateDir[-1] == "/" else templateDir
        bn = os.path.basename(templateDir)
        shutil.copytree(templateDir, os.path.join(os.getcwd(), bn))
        os.chdir(bn) # directory we just copied files to
        #print "jza555", os.getcwd()
        # Make the xml and txt parm file
        create_xml_parm_file(insrc, fieldset)
        
        # This is not necessary until v3.1
        hack_lock.acquire()
        if float(upp_version) > 3.0999:
            for fil in ["PostXMLPreprocessor.pl", "POST-XML-Library-NT.pl", 
                        "post_avblflds.xml"]:
                os.symlink(os.path.join(UPP_HOME, "parm", fil), fil)
                # the perl script seems to go back to the original working directory
                dep_file = os.path.join(g_exec_dir, fil)
                # UPDATE - this is causing race conditions
                if os.path.islink(dep_file):
                    os.unlink(dep_file)
                os.symlink(os.path.join(os.getcwd(), fil), dep_file)
        x2t_args = ["/usr/bin/perl", "PostXMLPreprocessor.pl", "postcntrl.xml", 
                    "post_avblflds.xml", "postxconfig-NT.txt"]
        postcntrl = os.path.join(g_exec_dir, "postcntrl.xml")
        if os.path.islink(postcntrl):
            os.unlink(postcntrl)
        os.symlink(os.path.join(os.getcwd(), "postcntrl.xml"), postcntrl)
        #import pdb ; pdb.set_trace()
        
        # For some reason, the XML->txt converter runs in the exec dir, so 
        # it's a critical section
        
        #subprocess.check_call(["echo","jza666"])
        #subprocess.check_call(["/bin/pwd"])
        #subprocess.check_call(["/bin/ls"])
        subprocess.check_call(x2t_args) #, shell=True)  
        shutil.copy(os.path.join(g_exec_dir,"postxconfig-NT.txt"), os.getcwd()+"/postxconfig-NT.txt")
        hack_lock.release()
        #p = subprocess.Popen(x2t_args, cwd=os.getcwd())
        
        # Run Unipost
        upp_exe = os.path.join(UPP_HOME, "bin", "unipost.exe")
        os.symlink(upp_exe, "unipost.exe")
        
        # this is done in the above commented code, so it must be uncommented when v3.1 works
        #os.symlink(os.path.join(UPP_HOME, "parm", "post_avblflds.xml"), "post_avblflds.xml")

        insrc.create_itag(fcst_offset, domain)
        run_unipost(insrc, fieldset, conf, fcst_offset, jobname)
        unipost_outfile = insrc.unipost_outfile_name(fcst_offset)
        #outfile = fieldset.get_outfile(conversion_args)
        #if not os.path.exists(os.path.dirname(outfile)):
        try:
                os.makedirs(os.path.dirname(outfile))
        except OSError:
                # another process/thread may have tried to create it at the same time
                assert os.path.exists(os.path.dirname(outfile))
        if INTERPOLATE_TO_LATLON:
            # ASSUME : data is staggered (True for NMB/NMM) TODO : Handle ARW
            latlon_outfile = unipost_outfile.lower()
            print "jza88888 latlon_outfile = ", latlon_outfile
            #(base,ext) = os.path.splitext(unipost_outfile)
            #staggered_outfile = base + ".nativeHorz" + ext
            #os.move(fieldset.outfile, staggered_outfile)
            #regrid_output(insrc, staggered_outfile, latlon_outfile, domain)
            #import pdb ; pdb.set_trace()
            log.debug("starting regrid")
            #hack: separate_files (see regrid_output())
            if "-multifield-" in outfile:
                separate_files = True
            else:
                separate_files = False
            regrid_output(insrc, unipost_outfile, latlon_outfile, domain, fieldset, separate_files, conf)
            log.debug("regrid complete")
            # hack: Change outfile for separate files case
            if  "-multifield-" in outfile:
                for pname in fieldset.pnames:
                    # hack as in regrid_output() - change prefix to have field.
                    # Note that there is a TODO there that would require a corresponding
                    # change here.
                    #
                    # NOTE: UGRD and VGRD can go in separate files, but have to do subset
                    # after regridding, not at the same time as is currently done. So 
                    # maybe that's the better option
                    ##if pname == "VGRD": 
                    ##    continue
                    ##elif pname == "UGRD":
                    ##    ll_outnow = latlon_outfile.replace("nmbprs", "nmbprs_winds")
                    ##else:
                    ##    ll_outnow = latlon_outfile.replace("nmbprs", "nmbprs_"+pname) 
                    ll_outnow = latlon_outfile.replace("nmbprs", "nmbprs_"+pname) 
                    outnow = outfile.replace("-multifield-", pname)
                    cat_file(ll_outnow, outnow)
            else:
                cat_file(latlon_outfile, outfile)

        # Retain the native domain output - will all go in one file
        if conf.has_option("BASIC", "unipost_output_path"):
            native_outfile = conf.get("BASIC", "unipost_output_path")
            if native_outfile: # not blank
                fhr = int(fcst_offset.total_seconds() / 3600)
                fmin = int(fcst_offset.total_seconds() % 3600 / 60)
                native_outfile = native_outfile.format(init_date=init_date, fhr=fhr, fmin=fmin)
                log.debug("Combining unipost outfile contents...{0}->{1}"
                          .format(unipost_outfile, native_outfile))
                cat_file(unipost_outfile, native_outfile)

def  _get_key(fieldset, domain, init_date, fcst_offset, outfile):
    return "::".join([`fieldset`, str(domain), `init_date`, str(fcst_offset), 
                       outfile])

#
# MAIN
#
if __name__ == "__main__":
    hack_lock = mp.Lock()
    g_debug_mode  = False
    g_exec_dir = os.getcwd()
    #import pdb ; pdb.set_trace()
    (db_file, config_files, log_level, conf_overrides) = _parse_args()
    log = _default_log(log_level)
    conf = ConfigParser()
    #conf.readfp(open("params.conf"))
    conf.read(config_files)
    confbasic = lambda x: conf.get("BASIC", x)
    # Override any config options set in cmdline
    for opt in conf_overrides:
        try:
            lhs,value = opt.split("=") 
            sec,item = lhs.split(".")
        except ValueError:
            raise Exception("Override option should be in format: section.item=value")
        conf.set(sec, item, value)

    # Set the succeeded_tasks list, which contains a list of tasks that
    # were verified as successful. A task in this case is an execution
    # of unipost.exe and wgrib for a given fieldset, domain,  
    # init_date, and forecast hour
    # TODO : gET from args
    if os.path.exists(db_file):
        log.info("Loading database of succeeded processes")
        #import pdb ; pdb.set_trace()
        succeeded_tasks = pickle.load(open(db_file, 'rb'))
    else:
        succeeded_tasks = {} # []

    init_date = datestr_to_datetime(confbasic("start_date"))
    duration = tdelta(hours=float(confbasic("duration")))
    interval = tdelta(hours=float(confbasic("interval")))
    domains = [int(x) for x in confbasic("domains").split(",")]
    duration_secs = int(duration.total_seconds())
    interval_secs =  int(interval.total_seconds())
    first_fhr = float(confbasic("first_fhr"))

    output_dir = confbasic("output_dir").replace("/", os.sep)
    #create_template_dir() # TODO - reduce chance of issues w/ future UPP ver.
    #ln -fs ${UNIPOST_HOME}/src/lib/g2tmpl/params_grib2_tbl_new params_grib2_tbl_new
    #ln -fs ${WRFPATH}/run/ETAMPNEW_DATA nam_micro_lookup.dat
    #ln -fs ${WRFPATH}/run/ETAMPNEW_DATA.expanded_rain hires_micro_lookup.dat
    # ALL the crtm stuff
    conversion_args = { "init_date":init_date} 
    model_dir = confbasic("model_rundir").format(**conversion_args)
    try:
        model_type = confbasic("model_type")
    except:
        model_type = guess_model_type(model_dir)
    if model_type in ("nmb", "nmmb"):
        insrc = NMMBInputSource(init_date, model_dir)
    elif model_type == "nmm":
        insrc = WRFNMMInputSource(init_date, model_dir)
    else:
        raise Exception("Unknown model_type")
    conversion_args["modelstr"] = insrc.modelstr 
    fieldsets = get_fieldsets(conf, insrc, init_date)
    
    
    first_fcst_sec = int(first_fhr * 3600.)
    last_fcst_sec = duration_secs + first_fcst_sec 
    dateRange = range(first_fcst_sec, last_fcst_sec+1, interval_secs)
    all_dates = [init_date + tdelta(seconds=curr) for curr in dateRange]
    log.debug("Will run the following dates: {0}".format(all_dates))
    simultaneous_mode = strtobool(confbasic("simultaneous_mode"))
    waiting_processes = collections.OrderedDict() # will only be used in simultaneous_mode 
    for currDate in all_dates:
        #import pdb ; pdb.set_trace()
        fcst_offset = currDate - init_date
        fhr = int(fcst_offset.total_seconds() / 3600)
        fcst_min = int(fcst_offset.total_seconds() % 3600 / 60)
        conversion_args.update({"fdate":currDate, "fhr":fhr, 
                                "fmin":fcst_min})
        log.debug("conversion_args: {0}".format(conversion_args))
        for domain in domains:
            conversion_args["domain"] = domain
            for fieldset in fieldsets:
                #import pdb ; pdb.set_trace()
                if len(fieldset.pnames) > 1:
                    # hack: Since we change the name for unipost
                    #conversion_args["pname"] = "multifield"
                    conversion_args["pname"] = "-multifield-"
                else:
                    conversion_args["pname"] = fieldset.pnames[0]
                # NOTE: fieldset.outfile is the name we want to give it, as 
                # specified in the config, not the default name given by UPP
                outfile = os.path.join(output_dir, fieldset.outfile_pattern)
                outfile = outfile.format(**conversion_args)
                
                # * TODO This doesn't work with non-unique outfiles, since after the first field(set) writes to
                #        it, the ones that come after will skip it
                # I guess make temprorary until all fieldsets are completed, but how to deal with 
                # simultaneous vs. non-simultaneous
                #  - keep DB of completed runs?
                #if os.path.exists(outfile):
                #    log.info("Skipping existing output file '{0}'. Remove it "
                ##             "if it must be re-run".format(outfile))
                #    continue
                
                log.info("Will write to {0}".format(outfile))
                # Run UPP
                jobname = "upp__d{dom:02d}_{initDate:%Y%m%d%H%M}_fhr{fhr:03d}_"\
                          .format(initDate=init_date, dom=domain, fhr=fhr)
                #jobname +=  '_'.join(fieldset.pnames)  ; not specific enuf
                jobname +=  '_'.join(fieldset.shortnames) 
                args = [fieldset, insrc, domain, init_date, fcst_offset,
                        template_dir, conf, outfile, jobname, hack_lock]
                
                key = _get_key(fieldset, domain, init_date, fcst_offset, outfile)
                #import pdb ; pdb.set_trace()
                if key in succeeded_tasks:
                    log.info("Skipping succeeded entry: {0}".format(args))
                    continue
                
                #log.info("Skipping already succeded fieldset: '{0}'"
                #import pdb ; pdb.set_trace()
                if simultaneous_mode:
                    currArgs = copy.copy(args) 
                    if strtobool(confbasic("log_to_file")):
                       currArgs.append(True) # last arg is optional arg to log to file
                    #t = threading.Thread(target=run_upp, name=jobname, args=args)
                    p = mp.Process(target=run_upp, name=jobname, args=currArgs)
                    #waiting_processes.append(p)
                    waiting_processes[key] = p
                    #process_keys.append(key)
                else:
                    #run_upp(fieldset, insrc, domain, init_date, fcst_offset, 
                    #        template_dir, conf, outfile)
                    run_upp(*args)

    # Submit and monitor processes
    # NOTE : This updates the "database" of succeeded fieldsets. It is done 
    # serially, but if another process is updating the same database, it
    # could cause it to get corrupted
    if simultaneous_mode: 
        running_procs = {} #[]
        failed_procs = [] # don't need key for this
        #waiting_processes.reverse() # so we start from beginning
        while len(waiting_processes) > 0 or len(running_procs) > 0:
            # Move jobs from waiting list to running list
            while len(running_procs) < MAX_JOBS and len(waiting_processes) > 0:
                k, curr_proc = waiting_processes.popitem()
                #running_procs.append(curr_proc)
                running_procs[k] = curr_proc 
                #curr_proc.start() # 
                running_procs[k].start()
            popable = []
            # Check status of running jobs
            for key,proc in running_procs.iteritems():
                if proc.exitcode is not None:
                    if proc.exitcode != 0:
                        failed_procs.append(proc)
                        # TODO : More descriptive info about proc (tempdir, fieldset, ...
                        log.warn("Process {0} failed with exit code {1}"
                                 .format(proc, proc.exitcode))
                        # TODO : Change overall exit status if any process fails?
                    #new
                    else:
                        #import pdb ; pdb.set_trace()
                        succeeded_tasks[key] = 'complete'
                        pickle.dump(succeeded_tasks, open(db_file, 'wb'))
                    popable.append(key)
            for k in popable:
                running_procs.pop(k)
            """
            # Pop procs that are done from `running_procs' and update succeeded_fieldsets
            # sort and go in reverse so there's no need to reindex after each del
            import pdb ; pdb.set_trace()
            #for pidx in sorted(popable, reverse=True):
            for pKey in popable
                #p = running_procs[pidx]
                p = running_procs[pKey]
                if p.exitcode == 0:
                    succeeded_tasks.append({pKey:running_procs[pKey]}) # TODO  verify wgrib output
                    pickle.dump(succeeded_tasks, open(db_file, 'wb'))
                #del running_procs[pidx]
                running_procs.pop(pKey)
            """
            time.sleep(JOB_POLL_INTERVAL)


