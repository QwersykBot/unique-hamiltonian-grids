"""Run one certificate producer shard into a deterministic gzip file, atomically."""
import gzip
from pathlib import Path
import shutil
import subprocess
import sys

if len(sys.argv)!=4:
    raise SystemExit('usage: compress_producer.py SHARD SHARDS OUTPUT.gz')
root=Path(__file__).resolve().parent
shard,shards=int(sys.argv[1]),int(sys.argv[2])
output=Path(sys.argv[3]).resolve()
temporary=output.with_suffix(output.suffix+'.partial')
summary=root/f'shard{shard}-summary.json'
command=[str(root/'certificate_producer'),'full',str(shard),str(shards),str(summary)]
with temporary.open('wb') as destination:
    with subprocess.Popen(command,stdout=subprocess.PIPE) as process:
        with gzip.GzipFile(fileobj=destination,mode='wb',filename='',compresslevel=9,mtime=0) as compressed:
            shutil.copyfileobj(process.stdout,compressed,length=1<<20)
        code=process.wait()
        if code:
            raise SystemExit(f'Producer exited {code}; incomplete output retained only as {temporary.name}')
temporary.replace(output)
print(f'COMPRESSED shard={shard} bytes={output.stat().st_size}',file=sys.stderr,flush=True)
