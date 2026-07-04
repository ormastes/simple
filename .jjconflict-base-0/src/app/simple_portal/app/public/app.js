async function loadPortal() {
  const seedEl = document.getElementById("seed");
  const metaEl = document.getElementById("meta");

  try {
    const examplesResp = await fetch("/api/portal/examples");
    const examplesJson = await examplesResp.json();
    const first = (examplesJson.examples || [])[0];
    seedEl.textContent = first ? first.source : "No example records";
  } catch (err) {
    seedEl.textContent = "Failed to load examples";
  }

  try {
    const releasesResp = await fetch("/api/portal/releases");
    const releasesJson = await releasesResp.json();
    metaEl.textContent = JSON.stringify(releasesJson, null, 2);
  } catch (err) {
    metaEl.textContent = "Failed to load releases";
  }
}

loadPortal();
