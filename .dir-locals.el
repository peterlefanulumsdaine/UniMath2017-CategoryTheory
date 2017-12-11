;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")

((coq-mode
  . ((eval . 
	   (let
	     (make-local-variable 'coq-prog-args)
	     (setq coq-prog-args `("-emacs" "-indices-matter" "-type-in-type" ))
	     (make-local-variable 'proof-prog-name-ask)
	     (setq proof-prog-name-ask `1))))))
