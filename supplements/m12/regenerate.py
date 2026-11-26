#!/usr/bin/env python3
"""Regenerate the complete certificate in a fresh directory, then verify it.

Requires a C++20 compiler. --sample exercises the producer on only the saved
partial sample and deliberately does not establish the lower bound/equality.
"""
import argparse
import concurrent.futures
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
import verify

FLAGS=['-O3','-DNDEBUG','-std=c++20','-Wall','-Wextra','-Wpedantic']


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sample',action='store_true',help='partial producer/verification smoke test only')
    parser.add_argument('--frontier',action='store_true',help='also run the optional independent upper frontier count')
    parser.add_argument('--cxx',default='g++')
    parser.add_argument('--workdir',type=Path,default=ROOT/'work')
    args=parser.parse_args()
    started=time.perf_counter()
    hashes=verify.validate_payload()
    verify.require(shutil.which(args.cxx) is not None,'C++20 compiler not found: '+args.cxx)
    checker=verify.load_source('check_certificate')
    frontier=verify.load_source('root_transfer') if args.frontier else None
    args.workdir.mkdir(parents=True,exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='regenerate-',dir=args.workdir.resolve()))
    for name in ['cycle_counter.cpp','certificate_producer.cpp','compress_producer.py',
                 'merge_certificates.py','producer-metadata.json']:
        relative='producer/'+name
        verify.require(relative in hashes,'Unhashed producer input: '+relative)
        shutil.copyfile(ROOT/relative,work/name)
    print('Generated files: '+str(work),file=sys.stderr,flush=True)
    binary=work/'certificate_producer'
    subprocess.run([args.cxx,*FLAGS,str(work/'certificate_producer.cpp'),'-o',str(binary)],check=True)
    if args.sample:
        cases=[]
        with gzip.open(ROOT/'data/sample-m12-hc-certificate.jsonl.gz','rt') as stream:
            next(stream)
            for line in stream:
                deleted=json.loads(line)[0]
                cases.append(str(len(deleted))+' '+' '.join(map(str,deleted))+'\n')
        result=subprocess.run([str(binary),'sample'],input=''.join(cases),text=True,capture_output=True,check=True)
        print(result.stderr.strip(),file=sys.stderr,flush=True)
        output=work/'sample-m12-hc-certificate.jsonl.gz'
        with output.open('wb') as destination:
            with gzip.GzipFile(fileobj=destination,mode='wb',filename='',compresslevel=9,mtime=0) as compressed:
                compressed.write(result.stdout.encode())
    else:
        def run(shard):
            subprocess.run([sys.executable,str(work/'compress_producer.py'),str(shard),'2',
                            str(work/f'shard{shard}-m12-hc-certificate.jsonl.gz')],cwd=work,check=True)
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            futures=[pool.submit(run,shard) for shard in (0,1)]
            for future in futures:future.result()
        with (work/'merge-stdout.json').open('w') as stream:
            subprocess.run([sys.executable,str(work/'merge_certificates.py')],cwd=work,stdout=stream,check=True)
        output=work/'complete-m12-hc-certificate.jsonl.gz'
    lower=checker.check([output],partial=args.sample)
    upper=verify.verify_upper(checker,frontier)
    report=verify.assemble_report(lower,upper,args.sample)
    report['generated_directory']=str(work)
    report['certificate_sha256']=verify.sha256(output)
    report['seconds']=time.perf_counter()-started
    (work/'regeneration-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
