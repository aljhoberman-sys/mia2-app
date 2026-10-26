(() => {
'use strict';

// Feedback goes by email through FormSubmit (formsubmit.co): free, no account for anyone, attachments up to 10 MB.
// FORM_ID is the random alias FormSubmit hands out once the address is confirmed, so the address stays out of the code.
const FORM_ID = 'dcd648970343d13fb7c1b7a134134b29';
const MAX_BYTES = 10 * 1024 * 1024;

const $ = id => document.getElementById(id);
const dlg = $('feedback'), form = $('fbForm'), list = $('fbFiles'), note = $('fbNote');
let files = [];

const kb = n => n < 1024 * 1024 ? Math.max(1, Math.round(n / 1024)) + ' KB' : (n / 1024 / 1024).toFixed(1) + ' MB';
const say = (msg, bad) => { note.textContent = msg || ''; note.classList.toggle('bad', !!bad); };

function showFiles() {
  list.replaceChildren(...files.map((f, i) => {
    const li = document.createElement('li');
    const x = document.createElement('button');
    x.type = 'button'; x.textContent = '×'; x.setAttribute('aria-label', 'Remove ' + f.name);
    x.onclick = () => { files.splice(i, 1); showFiles(); };
    li.append(f.name + ' (' + kb(f.size) + ')', x);
    return li;
  }));
}

function addFiles(more) {
  for (const f of more) files.push(f.name ? f : new File([f], 'pasted-image.png', { type: f.type }));
  showFiles(); say('');
}

function chartPicture() {
  const chart = $('chart'), mini = $('mini');
  const o = document.createElement('canvas');
  o.width = chart.width; o.height = chart.height + mini.height;
  const oc = o.getContext('2d');
  oc.fillStyle = getComputedStyle(document.documentElement).getPropertyValue('--panel').trim();
  oc.fillRect(0, 0, o.width, o.height);
  oc.drawImage(chart, 0, 0); oc.drawImage(mini, 0, chart.height);
  return new Promise(res => o.toBlob(b => res(new File([b], 'mia-chart.png', { type: 'image/png' }))));
}

function about() {
  const S = window.MIA && window.MIA.S;
  return [
    navigator.userAgent,
    'Screen ' + screen.width + '×' + screen.height + ', window ' + innerWidth + '×' + innerHeight,
    S ? S.pieces.length + ' piece(s) loaded' : '',
  ].filter(Boolean).join('\n');
}

function open() {
  const S = window.MIA && window.MIA.S;
  $('fbChartRow').hidden = !(S && S.pieces.length);
  say('');
  dlg.showModal();
  $('fbMessage').focus();
}

async function send(e) {
  e.preventDefault();
  if (!FORM_ID) { say('Feedback isn’t switched on yet in this copy of MIA 2.', true); return; }
  const message = $('fbMessage').value.trim();
  if (!message) { say('Please write a few words first.', true); $('fbMessage').focus(); return; }

  const attach = [...files];
  if ($('fbChart').checked && !$('fbChartRow').hidden) attach.push(await chartPicture());
  const total = attach.reduce((n, f) => n + f.size, 0);
  if (total > MAX_BYTES) { say('The attachments come to ' + kb(total) + '. The limit is 10 MB in all.', true); return; }

  // A plain multipart POST into a hidden frame is FormSubmit's documented way to send files, and keeps the page in place.
  const name = $('fbName').value.trim();
  const out = document.createElement('form');
  out.method = 'POST'; out.enctype = 'multipart/form-data'; out.target = 'fbFrame'; out.hidden = true;
  out.action = 'https://formsubmit.co/' + FORM_ID;
  const field = (k, v) => { const i = document.createElement('input'); i.type = 'hidden'; i.name = k; i.value = v; out.append(i); };
  field('name', name || '(not given)');
  field('email', $('fbEmail').value.trim());
  field('message', message);
  field('about', about());
  field('_subject', 'MIA 2 feedback' + (name ? ' from ' + name : ''));
  field('_template', 'table');
  field('_captcha', 'false');
  field('_honey', $('fbHoney').value);
  attach.forEach((f, i) => {
    const input = document.createElement('input');
    input.type = 'file'; input.name = 'attachment' + (i ? i + 1 : '');
    const dt = new DataTransfer(); dt.items.add(f); input.files = dt.files;
    out.append(input);
  });

  const go = $('fbSend');
  go.disabled = true; say('Sending…');
  const frame = $('fbFrame');
  const done = ok => {
    clearTimeout(timer); frame.onload = null; out.remove(); go.disabled = false;
    if (!ok) { say('No answer from the mail service. Check your connection and try again.', true); return; }
    form.reset(); files = []; showFiles();
    say('Thank you, your feedback has been sent.');
    setTimeout(() => { if (dlg.open) dlg.close(); say(''); }, 1800);
  };
  const timer = setTimeout(() => done(false), 60000);
  frame.onload = () => done(true);
  document.body.append(out);
  out.submit();
}

$('feedbackBtn').onclick = open;
$('fbCancel').onclick = () => dlg.close();
$('fbPick').onclick = () => $('fbInput').click();
$('fbInput').onchange = e => { addFiles([...e.target.files]); e.target.value = ''; };
form.onsubmit = send;
// screenshots can be pasted or dropped straight into the form; the drop stays here instead of loading as music
dlg.addEventListener('paste', e => {
  const imgs = [...e.clipboardData.files];
  if (imgs.length) { e.preventDefault(); addFiles(imgs); }
});
dlg.addEventListener('dragover', e => { e.preventDefault(); e.stopPropagation(); });
dlg.addEventListener('drop', e => { e.preventDefault(); e.stopPropagation(); addFiles([...e.dataTransfer.files]); });
dlg.addEventListener('click', e => { if (e.target === dlg) dlg.close(); });
})();
