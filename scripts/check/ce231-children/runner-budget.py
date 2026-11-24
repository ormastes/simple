"""Hosted single-owner build budget: measured availability, never a smoke clamp."""
import datetime,os,socket
from pathlib import Path
RESERVE_KIB=2*1024*1024
MIN_BUILD_KIB=6*1024*1024

def budget(available_kib):
    if type(available_kib) is not int or available_kib<=0:
        raise ValueError('invalid available memory sample')
    cap=min(available_kib*3//4,available_kib-RESERVE_KIB)
    if cap<MIN_BUILD_KIB:
        raise ValueError('host lacks bounded single-owner build headroom')
    return cap

def available():
    return int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:')))

def sample(role):
    value=available()
    return {'policy':'hosted-available-fraction-v1','role':role,'available_kib':value,
            'cap_kib':budget(value),'fraction_numerator':3,'fraction_denominator':4,
            'reserve_kib':RESERVE_KIB,'minimum_build_kib':MIN_BUILD_KIB,
            'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'host':socket.gethostname(),'run_id':os.environ.get('GITHUB_RUN_ID'),'pid':os.getpid()}

def recheck(cap_kib):
    value=available()
    if type(cap_kib) is not int or cap_kib<MIN_BUILD_KIB or cap_kib>value*3//4 or value-cap_kib<RESERVE_KIB:
        raise ValueError('host capacity changed before launch; refusing unchanged reservation')
    return value
