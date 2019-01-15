(TeX-add-style-hook
 "hrep"
 (lambda ()
   (TeX-run-style-hooks
    "tikz/hrep")
   (LaTeX-add-labels
    "sec:hrep"))
 :latex)

