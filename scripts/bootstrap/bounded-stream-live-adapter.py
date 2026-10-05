"""Inner pipe adapter for the reviewed bounded logger; outer owner owns CFEC."""
import hashlib,importlib.util,json,pathlib,queue,subprocess,threading,time

def diagnostic_evidence(output):
    """Compact verified evidence for result rows and failure triage, not verdicts."""
    output=pathlib.Path(output)
    receipt=json.loads((output/'stream.json').read_text(encoding='utf-8'))
    path=output/'diagnostics.json'
    assert pathlib.Path(receipt['diagnostic_summary_path']).resolve()==path.resolve()
    with path.open('rb') as source:data=source.read(512*1024+1)
    assert len(data)<=512*1024,'Default diagnostic summary exceeds bounded schema'
    assert hashlib.sha256(data).hexdigest()==receipt['diagnostic_summary_sha256']
    summary=json.loads(data)
    assert summary['schema']=='bounded-live-diagnostic-events-v1'
    assert summary['stream_sha256']==receipt['stream_sha256'] and summary['stream_bytes']==receipt['bytes_seen']
    assert summary['events_retained']==len(summary['records'])<=64
    assert summary['events_observed']==summary['events_retained']+summary['events_dropped']
    counts={}
    for row in summary['records']:
        marker=row['marker'].lower();counts[marker]=counts.get(marker,0)+1
    return dict(path=str(path),sha256=receipt['diagnostic_summary_sha256'],
                events_observed=summary['events_observed'],events_dropped=summary['events_dropped'],
                truncated_events=summary['truncated_events'],retained_markers=counts,
                excerpts=[dict(offset=r['offset'],text=r['text'][:512],truncated=r['truncated'] or len(r['text'])>512) for r in summary['records'][-4:]],
                qualification='OBSERVATION_ONLY_NOT_A_VERDICT')


def load_logger(path, expected_sha):
    path=pathlib.Path(path)
    with path.open('rb') as source:
        if hashlib.file_digest(source,'sha256').hexdigest()!=expected_sha:
            raise RuntimeError('Pinned bounded logger changed')
    spec=importlib.util.spec_from_file_location('pinned_windows_bounded_logger',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def run_bounded(command, output, logger_path, logger_sha, cap=4*1024*1024, cwd=None, *, summary_path, summary_sha):
    logger=load_logger(logger_path,logger_sha)
    summary_module=load_logger(summary_path,summary_sha)
    diagnostics=summary_module.DiagnosticStreamSummary()
    output=pathlib.Path(output);output.mkdir(exist_ok=False)
    def move(source,destination,replace):
        # Windows rename refuses an existing destination; later replacements
        # are limited to names the canonical observer itself already owns.
        source.replace(destination) if replace else source.rename(destination)
    chunks=queue.Queue(maxsize=8)
    reader_error=[]
    with (output/'retained.log').open('xb',buffering=0) as stream:
        retention=logger.BoundedLog(stream,cap,'truncate-drain')
        observer=logger.LiveLogObserver(output,'compiler','stream',65536,1.0,move)
        child=subprocess.Popen(command,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        def read_pipe():
            try:
                with child.stdout:
                    while True:
                        block=child.stdout.read1(65536)
                        if not block:break
                        chunks.put(block)
            except Exception as error:
                reader_error.append(repr(error))
            finally:chunks.put(None)
        reader=threading.Thread(target=read_pipe,daemon=True);reader.start()
        retention_error=None
        diagnostic_error=None
        while True:
            try:block=chunks.get(timeout=.25)
            except queue.Empty:
                observer.publish(retention,time.monotonic())
                continue
            if block is None:break
            if diagnostic_error is None:
                try:diagnostics.feed(block)
                except Exception as error:diagnostic_error=repr(error)[:2048]
            if retention_error is None:
                try:retention.feed(block)
                except Exception as error:retention_error=repr(error)
            else:
                # A primary log-write failure must not turn into backpressure
                # or terminate the compiler. Preserve the full stream digest
                # and explicitly reject the incomplete retained evidence.
                retention.observed+=len(block);retention.stream_hash.update(block)
            observer.feed(block)
            observer.publish(retention,time.monotonic())
        reader.join();code=child.wait()
        if retention_error is None:
            try:retention.finish()
            except Exception as error:retention_error=repr(error)
        observer.publish(retention,time.monotonic(),final=True,reason='child-exit',raw_status=code,native_status=code)
        diagnostic_sha=None
        if diagnostic_error is None:
            try:
                summary=diagnostics.finish()
                assert summary['stream_sha256']==retention.stream_hash.hexdigest()
                assert summary['stream_bytes']==retention.observed
                encoded=(json.dumps(summary,indent=2)+'\n').encode('utf-8')
                with (output/'diagnostics.json').open('xb') as evidence:evidence.write(encoded)
                diagnostic_sha=hashlib.sha256(encoded).hexdigest()
            except Exception as error:diagnostic_error=repr(error)[:2048]
        receipt=dict(schema='diagnostic-bounded-stream-live-v1',exit_code=code,
            bytes_seen=retention.observed,bytes_retained=retention.head_bytes+retention.tail_bytes,
            bytes_dropped=retention.observed-retention.head_bytes-retention.tail_bytes,
            stream_sha256=retention.stream_hash.hexdigest(),log_sha256=retention.log_hash.hexdigest(),
            capacity_bytes=cap,output_complete=not reader_error and retention_error is None and diagnostic_error is None,
            reader_errors=reader_error,retention_error=retention_error,live_observer_error=observer.error,
            diagnostic_summary_path=str(output/'diagnostics.json'),diagnostic_summary_sha256=diagnostic_sha,diagnostic_error=diagnostic_error,
            admitted=False,closure_authority='outer canonical Windows owner and native RSS receipt; this is observation only')
    (output/'stream.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    if reader_error or retention_error or diagnostic_error:
        raise RuntimeError('Compiler exited with incomplete bounded log evidence; see stream.json')
    return code
