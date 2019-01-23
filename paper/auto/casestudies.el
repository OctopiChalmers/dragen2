(TeX-add-style-hook
 "casestudies"
 (lambda ()
   (TeX-run-style-hooks
    "tikz/html")
   (LaTeX-add-labels
    "fig:html"))
 :latex)

