// The Gray Paper's own macros in the site's math (book: KaTeX; API: MathJax). The table is
// gp-macros.js, generated from the paper's TeX by scripts/gen_macros.py; build-site.sh loads it
// before this file. Formulas may use the paper's names, `¬` included (`$\wp¬authcode$`).
(function () {
  if (!window.gpMacros) return;
  var gp = window.gpMacros;

  // KaTeX (the book): every render gets the table; a page's own macros take precedence.
  if (typeof katex !== 'undefined' && !katex.__gpMacros) {
    var render = katex.render, toString = katex.renderToString;
    var base = null;
    var opts = function (o) {
      if (base === null) base = gp.katex({ renderToString: toString });
      var r = Object.assign({}, o || {});
      r.macros = Object.assign({}, base, r.macros || {});
      return r;
    };
    katex.render = function (tex, el, o) { return render.call(katex, gp.name(tex), el, opts(o)); };
    katex.renderToString = function (tex, o) { return toString.call(katex, gp.name(tex), opts(o)); };
    katex.__gpMacros = true;
  }

  // MathJax (the API pages): extend doc-gen4's configuration object before MathJax loads.
  if (typeof MathJax !== 'undefined' && !MathJax.version) {
    MathJax.tex = MathJax.tex || {};
    MathJax.tex.macros = Object.assign({}, gp.mathjax, MathJax.tex.macros || {});
    MathJax.startup = MathJax.startup || {};
    var ready = MathJax.startup.ready;
    MathJax.startup.ready = function () {
      if (ready) ready(); else MathJax.startup.defaultReady();
      MathJax.startup.document.inputJax.forEach(function (jax) {
        jax.preFilters.add(function (args) { args.math.math = gp.name(args.math.math); });
      });
    };
  }
})();
