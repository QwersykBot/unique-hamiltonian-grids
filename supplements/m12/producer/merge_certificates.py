"""Interleave two completed producer shards into one deterministic gzip certificate."""
import gzip
import hashlib
import json
from pathlib import Path
import time

ROOT=Path(__file__).resolve().parent
EXPECTED_HEADER={'format':'m12-hc-certificate-v1','n':12,'edge_order':'row-major-right-then-down'}
EXPECTED={0:(1,0,1),2:(666,70,596),4:(818316,215993,602323)}


def sha256(path):
    value=hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda:stream.read(1<<20),b''):value.update(block)
    return value.hexdigest()


def main():
    started=time.perf_counter()
    paths=[ROOT/f'shard{s}-m12-hc-certificate.jsonl.gz' for s in range(2)]
    summaries=[json.loads((ROOT/f'shard{s}-summary.json').read_text()) for s in range(2)]
    for s,summary in enumerate(summaries):
        if summary['shard']!=s or summary['shards']!=2:
            raise RuntimeError('Wrong shard metadata')
        if summary['canonical_by_d0_d2_d4']!=[1,666,818316]:
            raise RuntimeError('Wrong canonical totals')
    metadata=json.loads((ROOT/'producer-metadata.json').read_text())
    if sha256(ROOT/'cycle_counter.cpp')!=metadata['counter_source_sha256']:
        raise RuntimeError('Frozen counter source changed')
    if sha256(ROOT/'certificate_producer.cpp')!=metadata['producer_source_sha256']:
        raise RuntimeError('Producer source changed after sample validation')
    output=ROOT/'complete-m12-hc-certificate.jsonl.gz'
    temporary=output.with_suffix(output.suffix+'.partial')
    digest=hashlib.sha256();raw_bytes=0;counts={}
    with gzip.open(paths[0],'rb') as first,gzip.open(paths[1],'rb') as second,temporary.open('wb') as destination:
        streams=[first,second]
        headers=[stream.readline() for stream in streams]
        if any(json.loads(header)!=EXPECTED_HEADER for header in headers):
            raise RuntimeError('Wrong certificate header')
        with gzip.GzipFile(fileobj=destination,mode='wb',filename='',compresslevel=9,mtime=0) as compressed:
            def write(data):
                nonlocal raw_bytes
                compressed.write(data);digest.update(data);raw_bytes+=len(data)
            write(headers[0])
            for d,(total,expected_zero,expected_multiple) in EXPECTED.items():
                zero=multiple=0
                for ordinal in range(total):
                    line=streams[ordinal%2].readline()
                    if not line.endswith(b'\n'):raise RuntimeError('Missing/truncated record')
                    record=json.loads(line)
                    if not isinstance(record,list) or not isinstance(record[0],list) or len(record[0])!=d:
                        raise RuntimeError('Wrong record deletion size')
                    if len(record)==2 and type(record[1]) is int and record[1]==0:zero+=1
                    elif len(record)==3 and all(isinstance(x,str) and len(x)==66 and
                          all(c in '0123456789abcdef' for c in x) for x in record[1:]) and record[1]!=record[2]:multiple+=1
                    else:raise RuntimeError('Nonzero/nonmultiple record')
                    write(line)
                if (zero,multiple)!=(expected_zero,expected_multiple):raise RuntimeError('Classification totals differ from frozen result')
                counts[d]={'records':total,'zero':zero,'multiple':multiple}
            if any(stream.read(1) for stream in streams):raise RuntimeError('Extra records after expected coverage')
    temporary.replace(output)
    report={'format':EXPECTED_HEADER,'records':sum(x['records'] for x in counts.values()),
            'by_deletion_count':counts,'cycle_witnesses':2*sum(x['multiple'] for x in counts.values()),
            'gzip_bytes':output.stat().st_size,'gzip_sha256':sha256(output),
            'uncompressed_bytes':raw_bytes,'uncompressed_sha256':digest.hexdigest(),
            'shard_gzip_sha256':[sha256(path) for path in paths],
            'producer_source_sha256':metadata['producer_source_sha256'],
            'counter_source_sha256':metadata['counter_source_sha256'],
            'total_producer_cpu_seconds':sum(s['process_cpu_seconds'] for s in summaries),
            'max_producer_wall_seconds':max(s['wall_seconds'] for s in summaries),
            'merge_seconds':time.perf_counter()-started,
            'independent_verification_status':'Pending; merger checks format/totals, not certificate soundness.'}
    (ROOT/'certificate-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
