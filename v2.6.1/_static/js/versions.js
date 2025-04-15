function renderVersions(versions) {
  return `
  <dl>
    <dt>Versions</dt>${ versions.active.map((version) => `
    <dd ${ version.slug == versions.current.slug ? 'class="rtd-current-item"' : '' }>
      <a href="${ version.url }">${ version.slug }</a>
    </dd>
    `).join("\n")}
  </dl>
  `;
}

document.addEventListener('DOMContentLoaded', function () {
  $.getJSON('/alt-ergo/versions.json', (active) => {
    const versions = {
      "active": active,
      "current": JSON.parse(document.getElementById('CURRENT_VERSION').innerHTML),
    };

    document.body.insertAdjacentHTML("beforeend", `
    <div class="rst-versions" data-toggle="rst-versions" role="note" aria-label="Versions">
      <span class="rst-current-version" data-toggle="rst-current-version">
        <span class="fa fa-book"> Current version</span>
        ${ versions.current.slug }
        <span class="fa fa-caret-down"></span>
      </span>
      <div class="rst-other-versions">
        ${renderVersions(versions)}
      </div>
    </div>
    `);
  });
});
