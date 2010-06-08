;; ===== clops-mode
(defvar clops-mode-hook nil)
(defvar clops-mode-map
  (let ((clops-mode-map (make-keymap)))
    (define-key clops-mode-map "\C-j" 'newline-and-indent)
    clops-mode-map)
  "Keymap for CLOPS major mode")

(add-to-list 'auto-mode-alist '("\\.clo\\'" . clops-mode))

(defconst clops-font-lock-keywords-1
  (list 
   '("\\<NAME::" . font-lock-builtin-face)
   '("\\<ARGS::" . font-lock-builtin-face)
   '("\\<FORMAT::" . font-lock-builtin-face)
   '("\\<WHERE::" . font-lock-builtin-face)
   '("\\<FLY::" . font-lock-builtin-face)
   '("\\<OVERRIDES::" . font-lock-builtin-face)
   '("\\<VALIDITY::" . font-lock-builtin-face)
   '("\\<PACKAGE::" . font-lock-builtin-face)
  ) 
  "Minimal highlighting expressions for CLOPS mode.")

(defvar clops-font-lock-keywords clops-font-lock-keywords-1 "Default highlighting expressions for CLOPS mode.")

(defun clops-mode ()
  (interactive)
  (kill-all-local-variables)
  (use-local-map clops-mode-map)
  ;; Set up font-lock
  (set (make-local-variable 'font-lock-defaults) '(clops-font-lock-keywords))
  (setq major-mode 'clops-mode)
  (setq mode-name "CLOPS")
  (run-hooks 'clops-mode-hook))

(provide 'clops-mode)

(setq comment-start "/\*")
(setq comment-end "\*/")
;; ===== end of clops-mode
