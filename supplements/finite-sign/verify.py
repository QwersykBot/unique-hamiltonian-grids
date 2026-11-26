#!/usr/bin/env python3
"""Verify immutable payloads and replay both all-length certificates."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not __debug__:
    raise SystemExit("Run without -O, -OO or PYTHONOPTIMIZE.")
root=Path(__file__).resolve().parent
manifest=json.loads((root/"manifest.json").read_text())
for row in manifest["files"]:
    p=root/row["path"]
    if p.stat().st_size != row["bytes"] or hashlib.sha256(p.read_bytes()).hexdigest()!=row["sha256"]:
        raise SystemExit("Payload mismatch: "+row["path"])
results=[]
for command in ([sys.executable,str(root/"m8/verify_k8_published_sign.py")],
                [sys.executable,str(root/"m10/verify_sign_certificate.py"),"--repository",str(root/"source_model")]):
    run=subprocess.run(command,check=True,capture_output=True,text=True)
    result=json.loads(run.stdout)
    if result.get("status")!="PASS":raise SystemExit("Certificate did not pass")
    results.append(result)
print(json.dumps({"status":"PASS","payloads_verified":len(manifest["files"]),"certificates":results},indent=2))
