#!/usr/bin/env python3
"""Rebuild every distributed proof module and audit the declared axioms.

Run after lake update and lake exe cache get:
    lake env python3 build_verify.py
An existing pinned public dependency cache can be supplied read-only with
--dependency-project. No compiled research module from that project is used.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, subprocess, time
ROOT=Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--lean')
 parser.add_argument('--dependency-project',type=Path)
 args=parser.parse_args()
 compiler=args.lean or shutil.which('lean')
 if not compiler:raise SystemExit('Lean unavailable; install the pinned toolchain with elan.')
 manifest=json.loads((ROOT/'verification_manifest.json').read_text())
 version=subprocess.check_output([compiler,'--version'],cwd=ROOT,text=True).strip()
 assert 'version 4.35.0-rc2,' in version,version
 dep=(args.dependency_project or ROOT).resolve()
 pin=subprocess.check_output(['git','-C',str(dep/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
 assert pin==manifest['mathlib_revision'],(pin,manifest['mathlib_revision'])
 for item in manifest['sources']:
  path=ROOT/item['path'];assert sha(path)==item['source_sha256'],item['path']
  text=path.read_text()
  text=re.sub(r'/\-.*?\-/','',text,flags=re.S)
  text=re.sub(r'--[^\n]*','',text)
  assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|unsafe|extern|axiom)\b',text),item['path']
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
 build=ROOT/'build'/stamp;compiled=build/'compiled';logs=build/'logs'
 compiled.mkdir(parents=True);logs.mkdir()
 paths=[compiled,ROOT/'lean']+sorted((dep/'.lake/packages').glob('*/.lake/build/lib/lean'))
 env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
 start=time.monotonic();records=[]
 for i,module in enumerate(manifest['build_order'],1):
  source=ROOT/'lean'/(module+'.lean');before=sha(source);output=compiled/(module+'.olean')
  result=subprocess.run([compiler,'--root='+str(ROOT/'lean'),'-o',str(output),str(source)],cwd=ROOT/'lean',env=env,capture_output=True,text=True,timeout=300)
  log=result.stdout+result.stderr;(logs/(module+'.txt')).write_text(log)
  assert sha(source)==before,'Source changed during build: '+module
  if result.returncode:print(log,flush=True);raise SystemExit(module+' failed')
  records.append({'module':module,'source_sha256':before,'olean_sha256':sha(output),'exit_code':0})
  print(f'[{i}/{len(manifest["build_order"])}] {module}: kernel checked',flush=True)
 audit=(logs/'Verification.txt').read_text()
 matches=re.findall(r"^'(.*)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",audit,re.M)
 axioms={name:sorted({x.strip() for x in values.split(',') if x.strip()}) for name,values in matches}
 for rec in manifest['declarations']:
  assert rec['name'] in axioms,'Missing axiom audit: '+rec['name']
 for name,values in axioms.items():assert set(values)<=ALLOWED,(name,values)
 main_name=manifest['main_theorem'];assert main_name in axioms
 out={'status':'FULL_MAIN_THEOREM_KERNEL_CHECKED','checked_at_UTC':stamp,'compiler_version':version,'mathlib_revision':pin,'modules_rebuilt':records,'declarations_audited':len(manifest['declarations']),'axioms_by_declaration':axioms,'main_theorem':main_name,'main_axioms':axioms[main_name],'elapsed_seconds':round(time.monotonic()-start,2),'compiled_research_inputs':'none: fresh per-run directory; dependency-project research outputs excluded','logs_directory':str(logs.relative_to(ROOT))}
 (build/'rebuild_verification.json').write_text(json.dumps(out,indent=2)+'\n')
 (ROOT/'build/latest_verification.json').write_text(json.dumps(out,indent=2)+'\n')
 print('PASS: '+str(len(records))+' modules rebuilt; '+str(len(axioms))+' declarations audited.',flush=True)
 print('Main theorem axioms: '+', '.join(axioms[main_name]),flush=True)
if __name__=='__main__':main()
