;;; esml-mode.el --- Major mode for editing esml  -*- lexical-binding: t; coding: utf-8 -*-


(defgroup esml ()
  "IDE for esml"
  :group 'languages)

(defface esml-faces-locked
  '((t (:background "slate gray")))
  :group 'esml)

(defvar esml-buffer-loaded nil)
(defvar esml-hole-list nil)


(defvar inf-esml-seen-prompt nil)

(defun inf-esml-wait-for-prompt (proc &optional timeout)
  "Wait until PROC sends us a prompt.
The process PROC should be associated to a comint buffer."
  (with-current-buffer (process-buffer proc)
    (while (progn
             (goto-char comint-last-input-end)
             (not (or inf-esml-seen-prompt
                      (setq inf-esml-seen-prompt
                            (re-search-forward comint-prompt-regexp nil t))
                      (not (accept-process-output proc timeout))))))
    (unless inf-esml-seen-prompt
      (error "Can't find the prompt"))))

(defun inf-esml-send-command (proc str)
  (setq str (concat str "\n"))
  (with-current-buffer (process-buffer proc)
    (inf-esml-wait-for-prompt proc)
    (goto-char (process-mark proc))
    (insert-before-markers str)
    (move-marker comint-last-input-end (point))
    (setq inf-esml-seen-prompt nil)
    (comint-send-string proc str)))

(defun inf-esml-get-result (inf-expr)
  "Submit the expression `inf-expr' to the repl and read the result."
  (let ((proc (get-buffer-process "*inferior esml*")))
    (with-current-buffer (process-buffer proc)
      (let ((parsing-end                ; Remember previous spot.
             (marker-position (process-mark proc))))
        (inf-esml-send-command proc inf-expr)
        ;; Find new point.
        (inf-esml-wait-for-prompt proc)
        (goto-char (point-max))
        ;; Back up to the previous end-of-line.
        (end-of-line 0)
        ;; Extract the output
        (buffer-substring-no-properties
         (save-excursion (goto-char parsing-end)
                         (line-beginning-position 2))
         (point))))))

(defun esml-fill-hole (num expr)
  (when esml-buffer-loaded
    (let ((hole (nth num esml-hole-list)))
      (when hole
        (save-excursion
          (goto-char (car hole))
          (delete-region (point) (cdr hole))
          (insert expr))
        (esml-load-file)))))

(defun esml-refine-hole (num)
  (interactive "n")
  (when esml-buffer-loaded
    (let ((hole (nth num esml-hole-list)))
      (when hole
        (let* ((contents (buffer-substring (+ (car hole) 2) (- (cdr hole) 1)))
               (command  (concat ":refine " (int-to-string num) " " contents))
               (result   (inf-esml-get-result command)))
          (print contents)
          (print result)
          (save-excursion
            (goto-char (car hole))
            (delete-region (point) (cdr hole))
            (insert (concat "(" contents ")")))
          (esml-load-file))))))

(defun esml-next-hole ()
  "Move cursor to the next hole."
  (interactive)
  (message "esml-next-hole")
  (when esml-buffer-loaded
    (let ((holes esml-hole-list)
          (moved nil))
      (while (and holes (not moved))
        (let ((nexth (+ (caar holes) 2)))
          (if (< (point) nexth)
              (progn
                (goto-char nexth)
                (setq moved 't))
            (setq holes (cdr holes)))))
      (if (and (not moved) esml-hole-list)
          (goto-char (+ (caar esml-hole-list) 2))))))

(defun esml-prev-hole ()
  "Move cursor to the previous hole."
  (interactive)
  (message "esml-prev-hole")
  (when (and esml-buffer-loaded esml-hole-list)
    (if (<= (point) (- (cdar esml-hole-list) 1))
        (goto-char (+ (caar (last esml-hole-list)) 2))
      (let ((holes (cdr esml-hole-list))
            (lasth (+ (caar esml-hole-list) 2)))
        (while (and holes (> (point) (- (cdar holes) 1)))
          (setq lasth (+ (caar holes) 2)
                holes (cdr holes)))
        (goto-char lasth)))))

(defun esml-proc-load-buffer ()
  "Send the buffer into the esml interpreter"
  (interactive)
  (save-buffer)
  (let ((command (concat ":load \"" (buffer-file-name) "\"")))
    (inf-esml-get-result command))
  t)

(defun esml-proc-holes ()
  "Retrieve position information for holes from the interpreter."
  (interactive)
  (when esml-buffer-loaded
    (let* ((command ":holes")
           (result (inf-esml-get-result command)))
      (car (read-from-string result)))))

(defun esml-load-file ()
  "Load the buffer."
  (interactive)
  (when (esml-proc-load-buffer)
    (setq esml-buffer-loaded t)
    (let ((lock-overlay (make-overlay (point-min) (point-max)))
          (hook (lambda (&rest unused)
                  (setq esml-hole-list nil
                        esml-buffer-loaded nil)
                  (remove-overlays (point-min) (point-max) 'name 'esml-lock))))
                  ;; TODO: does this really kill the overlay?
      (overlay-put lock-overlay 'name 'esml-lock)
      (overlay-put lock-overlay 'face 'esml-faces-locked)
      (overlay-put lock-overlay 'modification-hooks (list hook))
      (overlay-put lock-overlay 'insert-in-front-hooks
                   (list (lambda (ov post start end &rest unused)
                           (when (equal (point-min) start)
                             (funcall hook)
                             (when (equal post 't)
                               (remove-overlays start end 'name 'esml-lock)))))))
    (let ((holes (esml-proc-holes))
          (doit (lambda (hole)
                  (let ((new-start (make-marker))
                        (new-end (make-marker)))
                    (set-marker new-start (+ (car hole) 2))
                    (set-marker new-end (- (cdr hole) 1))
                    (remove-overlays new-start new-end 'name 'esml-lock)))))
      (mapc doit holes)
      (setq esml-hole-list holes))))

;;; inferior esml stuff

(defvar esml-prog-file-path
  "~/projects/sml/esml/repl"
  "Path to esml interpreter")

(defvar esml-prog-arguments '()
  "Command-line arguments to pass to `repl'")

(defvar esml-prog-mode-map
  (let ((map (nconc (make-sparse-keymap) comint-mode-map)))
    (define-key map "\t" 'completion-at-point)
    map)
  "Basic mode map for `inf-esml'")

(defvar esml-prog-prompt-regexp "^-[0-9]*->"
  "Prompt for `inf-esml'")

(defun run-inf-esml ()
  "Run an inferior instance of `inf-esml' inside Emacs."
  (interactive)
  (let* ((esml-program esml-prog-file-path)
         (buf-name "*inferior esml*")
         (buf-live (comint-check-proc buf-name)))
    ;; pop to the "*inferior esml*" buffer if the process is dead, the
    ;; buffer is missing or it's got the wrong mode.
    (pop-to-buffer (get-buffer-create buf-name))
    ;; create the comint process if there is no buffer.
    (unless buf-live
      (apply 'make-comint-in-buffer "inferior esml" (current-buffer)
             esml-program esml-prog-arguments)
      (inf-esml-mode))
    (setq esml-prog-proc--buffer (current-buffer))))

(defun esml-prog--initialize ()
  "Helper fn to initialize esml repl"
  (setq comint-process-echoes t)
  (setq comint-use-prompt-regexp t))

(define-derived-mode inf-esml-mode comint-mode "inferior esml"
  "Major mode for esml repl.

\\<esml-prog-mode-map>"
  nil "inferior esml"
  ;; set the prompt
  (setq comint-prompt-regexp esml-prog-prompt-regexp)
  (setq comint-prompt-read-only t)
  ;; this makes it so commands like M-{ and M-} work.
  (set (make-local-variable 'paragraph-separate) "\\'")
  ;; (set (make-local-variable 'font-lock-defaults) '(esml-prog-font-lock-keywords t))
  (set (make-local-variable 'paragraph-start) esml-prog-prompt-regexp))

(add-hook 'esml-prog-mode-hook 'esml-prog--initialize)
