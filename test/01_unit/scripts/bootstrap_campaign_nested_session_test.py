import pathlib,subprocess,os,json,tempfile
s=pathlib.Path(__file__).resolve().parents[3]
r=pathlib.Path(tempfile.mkdtemp(prefix='campaign-session-regression-'))
leaf=r/'leaf.sh'; leaf.write_text('#!/bin/sh\n[ -n "$SIMPLE_BOOTSTRAP_SESSION_ID" ] || exit 7\nsleep 1\nexit 0\n')
driver=r/'driver.sh'
driver.write_text('. "'+str(s/'scripts/bootstrap/bootstrap-verification-campaign.shs')+'"\nbootstrap_verification_campaign_run 15 "$1" "'+str(leaf)+'" "'+str(s/'scripts/bootstrap')+'"\n')
env=os.environ.copy()
for k in list(env):
    if k.startswith('SIMPLE_BOOTSTRAP_SESSION_'): del env[k]
for name,nested in [('standalone',False),('nested',True)]:
    work=r/name; work.mkdir()
    cmd=['sh',str(driver),str(work)]
    if nested:
        cmd=['perl',str(s/'scripts/resource/process-tree-rss-watchdog.pl'),'--timeout-seconds=25','--receipt='+str(work/'outer.env'),'--',*cmd]
    with (work/'log').open('w') as log:
        rc=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=35).returncode
    receipts=list(work.glob('campaign.*/process.env'))
    assert rc==0,(name,rc)
    assert len(receipts)==1
    values=dict(l.split('=',1) for l in receipts[0].read_text().splitlines() if '=' in l)
    assert values['status']=='complete' and values['exit_status']=='0' and values['quiescent']=='1'
    assert values['session_mode']==('inherit' if nested else 'new')
    if nested:
        outer=dict(l.split('=',1) for l in (work/'outer.env').read_text().splitlines() if '=' in l)
        assert outer['status']=='complete' and outer['unexpected_session_pids']==''
        assert outer['session_id']==values['session_id']
    print(name,'PASS',flush=True)
(r/'result.json').write_text(json.dumps({'status':'PASS','scope':'real standalone and nested campaign watchdog session containment; no compiler qualification'}))
