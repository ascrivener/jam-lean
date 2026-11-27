// Render every macro of the GP macro table in KaTeX and MathJax 3 and report the ones that fail.
// A development check (not run in CI, which only checks that the table matches the paper):
// run it after changing scripts/gen_macros.py or moving to a new paper version.
//
//   cd docs/site && npm install --no-save mathjax-full@3.2.2 && node check-macros.js [formula ...]
//
// KaTeX is the copy Verso bundles (build the book first: _site/book/-verso-data/katex/katex.js).
// With formulas as arguments, renders those instead (paper names, ¬ included).
const path = require('path');
global.window = {};
require(path.join(__dirname, 'gp-macros.js'));
const table = require(path.join(__dirname, 'gp-macros.json')).macros;
const katex = require(path.join(__dirname, '_site/book/-verso-data/katex/katex.js'));
const {mathjax} = require('mathjax-full/js/mathjax.js');
const {TeX} = require('mathjax-full/js/input/tex.js');
const {SVG} = require('mathjax-full/js/output/svg.js');
const {liteAdaptor} = require('mathjax-full/js/adaptors/liteAdaptor.js');
const {RegisterHTMLHandler} = require('mathjax-full/js/handlers/html.js');
const {AllPackages} = require('mathjax-full/js/input/tex/AllPackages.js');
const adaptor = liteAdaptor();
RegisterHTMLHandler(adaptor);
const tex = new TeX({packages: AllPackages.filter(p => p !== 'bussproofs'), macros: window.gpMacros.mathjax,
                     formatError: (jax, err) => { throw err; }});
const doc = mathjax.document('', {InputJax: tex, OutputJax: new SVG({fontCache: 'none'})});
const km = window.gpMacros.katex(katex);
const args = process.argv.slice(2);
// Each macro with sample arguments, inside \left( … \right) so that \middle-based ones (\with) parse.
const forms = args.length ? args : Object.entries(table).map(([k, e]) =>
  '\\left( \\' + k + '{x}'.repeat(e.args - (e.default !== undefined ? 1 : 0)) + ' \\right)');
let kbad = 0, mbad = 0;
for (const f0 of forms) {
  const f = window.gpMacros.name(f0);
  try { katex.renderToString(f, {macros: Object.assign({}, km), throwOnError: true, strict: 'ignore'}); }
  catch (e) { kbad++; console.log('KaTeX  ', f0, '::', e.message.slice(0, 120)); }
  try {
    const s = adaptor.outerHTML(doc.convert(f, {display: false}));
    if (/merror|data-mjx-error|mathcolor="red"|fill="red"/.test(s)) throw new Error('error or undefined macro');
  } catch (e) { mbad++; console.log('MathJax', f0, '::', String(e.message).slice(0, 120)); }
}
console.log(`${forms.length} formulas; KaTeX errors ${kbad}; MathJax errors ${mbad}`);
process.exit(kbad || mbad ? 1 : 0);
