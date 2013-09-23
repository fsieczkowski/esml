;;; esml-mode.el --- Major mode for editing esml  -*- lexical-binding: t; coding: utf-8 -*-


(defgroup esml ()
  "IDE for esml"
  :group 'languages)

(defface esml-faces-locked
  '((t (:background "slate gray")))
  :group 'esml)

(defface esml-faces-active-hole
  '((t (:background "red")))
  :group 'esml)

(defvar esml-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-l" 'esml-load-file)
    (define-key map "\C-c\C-n" 'esml-next-hole)
    (define-key map "\C-c\C-p" 'esml-prev-hole)
    (define-key map "\C-c\C-s" 'esml-case-active-hole)
    (define-key map "\C-c\C-r" 'esml-refine-active-hole)
    (define-key map "\C-c\C-a" 'esml-apply-active-hole)
    (define-key map "\C-c\C-i" 'run-inf-esml)
    map))


(defvar esml-buffer-loaded nil)
(defvar esml-hole-list nil)
(defvar esml-active-hole nil)

(defun fill-hole (hole expr)
  (save-excursion
    (goto-char (- (car hole) 2))
    (delete-region (point) (+ (cdr hole) 1))
    (insert expr)
    (esml-load-file)))

(defun handle-errors (err)
  (let* ((buf (get-buffer-create "*esml errors*")))
    (display-buffer buf)
    (with-current-buffer buf
      (delete-region (point-min) (point-max))
      (insert err))))

(defun show-current-hole ()
  "Prints the current hole information in the *esml holes* buffer"
  (interactive)
  (unless (null esml-active-hole)
    (let* ((buf (get-buffer-create "*esml holes*"))
           (command (concat ":show " (int-to-string esml-active-hole)))
           (data (car (read-from-string (inf-esml-get-result command)))))
      (pcase data
        (`(ok ,s) (progn
                    (display-buffer buf)
                    (with-current-buffer buf
                      (delete-region (point-min) (point-max))
                      (insert s))))
        (`(error ,err) (handle-errors err))))))

(defun esml-refine-hole (num)
  (when esml-buffer-loaded
    (let ((hole (nth num esml-hole-list)))
      (when hole
        (let* ((contents (buffer-substring (car hole) (cdr hole)))
               (command  (concat ":refine " (int-to-string num) " " contents))
               (result   (inf-esml-get-result command)))
          (fill-hole hole (concat "(" contents ")")))))))

(defun esml-refine-active-hole ()
  (interactive)
  (unless (null esml-active-hole)
    (esml-refine-hole esml-active-hole)))

(defun esml-apply-hole (num)
  (when esml-buffer-loaded
    (let ((hole (nth num esml-hole-list)))
      (when hole
        (let* ((contents (buffer-substring (car hole) (cdr hole)))
               (command  (concat ":apply " (int-to-string num) " " contents))
               (resultS  (inf-esml-get-result command))
               (result   (car (read-from-string resultS))))
          (pcase result
            (`(ok ,expr) (fill-hole hole expr))
            (`(error ,err) (handle-errors err))))))))

(defun esml-apply-active-hole ()
  (interactive)
  (unless (null esml-active-hole)
    (esml-apply-hole esml-active-hole)))

(defun esml-case-hole (num)
  (when esml-buffer-loaded
    (let ((hole (nth num esml-hole-list)))
      (when hole
        (let* ((contents (buffer-substring (car hole) (cdr hole)))
               (command  (concat ":case " (int-to-string num) " " contents))
               (resultS  (inf-esml-get-result command))
               (result   (car (read-from-string resultS))))
          (pcase result
            (`(ok ,expr) (fill-hole hole expr))
            (`(error ,err) (message err))))))))

(defun esml-case-active-hole ()
  (interactive)
  (unless (null esml-active-hole)
    (esml-case-hole esml-active-hole)))

(defun esml-next-hole-from-pos ()
  "Move cursor to the hole after the point, return its number and
delimiting markers."
  (interactive)
  (when (and esml-buffer-loaded esml-hole-list)
    (let ((holes esml-hole-list)
          (moved nil)
          (num 0)
          (hole nil))
      (while (and holes (not moved))
        (let ((nexth (caar holes)))
          (if (< (point) nexth)
              (progn
                (goto-char nexth)
                (setq hole (car holes)
                      moved 't))
            (setq num (+ num 1)
                  holes (cdr holes)))))
      (if (and (not moved) esml-hole-list)
          (progn
            (goto-char (caar esml-hole-list))
            (cons 0 (car esml-hole-list)))
        (cons num hole)))))

(defun esml-next-hole ()
  (interactive)
  (when (and esml-buffer-loaded esml-hole-list)
    (if (null esml-active-hole)
        (let ((nh (esml-next-hole-from-pos)))
          (mark-active (cdr nh))
          (setq esml-active-hole (car nh)))
      (let ((nh (nth (+ esml-active-hole 1) esml-hole-list))
            (oh (nth esml-active-hole esml-hole-list)))
        (if (null nh)
            (setq nh (car esml-hole-list)
                  esml-active-hole 0)
          (setq esml-active-hole (+ esml-active-hole 1)))
        (goto-char (car nh))
        (mark-active nh)
        ))
    (show-current-hole)))

(defun esml-prev-hole-from-pos ()
  "Move cursor to the hole before the point, return number and delimiting markers."
  (interactive)
  (when (and esml-buffer-loaded esml-hole-list)
    (if (<= (point) (cdar esml-hole-list))
        (let ((hole (car (last esml-hole-list)))
              (num  (length esml-hole-list)))
          (goto-char (car hole))
          (cons num hole))
      (let ((holes (cdr esml-hole-list))
            (lasth (car esml-hole-list))
            (num   0))
        (while (and holes (> (point) (cdar holes)))
          (setq lasth (car holes)
                holes (cdr holes)
                num   (+ num 1)))
        (goto-char (car lasth))
        (cons num lasth)))))

(defun esml-prev-hole ()
  (interactive)
  (when (and esml-buffer-loaded esml-hole-list)
    (if (null esml-active-hole)
        (let ((nh (esml-prev-hole-from-pos)))
          (mark-active (cdr nh))
          (setq esml-active-hole (car nh)))
      (let ((nh  nil)
            (oh  nil)
            (num nil))
        (if (= esml-active-hole 0)
            (setq nh (car (last esml-hole-list))
                  oh (car esml-hole-list)
                  num (- (length esml-hole-list) 1))
          (setq nh (nth (- esml-active-hole 1) esml-hole-list)
                oh (nth esml-active-hole esml-hole-list)
                num (- esml-active-hole 1)))
        (mark-active nh)
        (goto-char (car nh))
        (setq esml-active-hole num)))
    (show-current-hole)))

(defun esml-proc-load-buffer ()
  "Send the buffer into the esml interpreter"
  (interactive)
  (save-buffer)
  (if (null (get-buffer-process "*inferior esml*"))
      (progn
        (message "Inferior esml not started. Start the process first.")
        nil)
    (let ((command (concat ":load \"" (buffer-file-name) "\"")))
      (inf-esml-get-result command)
      t)))

(defun esml-proc-holes ()
  "Retrieve position information for holes from the interpreter."
  (interactive)
  (when esml-buffer-loaded
    (let* ((command ":holes")
           (result (inf-esml-get-result command)))
      (car (read-from-string result)))))

(defun mark-active (hole)
  (remove-overlays (point-min) (point-max) 'name 'esml-hole)
  (let ((hole-overlay (make-overlay (car hole) (cdr hole))))
    (overlay-put hole-overlay 'name 'esml-hole)
    (overlay-put hole-overlay 'face 'esml-faces-active-hole)))

(defun esml-load-file ()
  "Load the buffer."
  (interactive)
  (setq esml-hole-list nil
        esml-active-hole nil
        esml-buffer-loaded nil)
  (when (esml-proc-load-buffer)
    (setq esml-buffer-loaded t)
    (let ((lock-overlay (make-overlay (point-min) (point-max)))
          (hook (lambda (&rest unused)
                  (setq esml-hole-list nil
                        esml-buffer-loaded nil)
                  (remove-overlays (point-min) (point-max) 'name 'esml-hole)
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
                    (remove-overlays new-start new-end 'name 'esml-lock)
                    (cons new-start new-end)))))
      (setq esml-hole-list (mapcar doit holes)))))

;;;###autoload
(define-derived-mode esml-mode prog-mode "ESML")

;;; inferior esml stuff

(require 'comint)

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

(defun run-inf-esml (&optional nopop)
  "Run an inferior instance of `inf-esml' inside Emacs."
  (interactive)
  (let* ((esml-program esml-prog-file-path)
         (buf-name "*inferior esml*")
         (buf-live (comint-check-proc buf-name))
         (buf (get-buffer-create buf-name)))
    ;; pop to the "*inferior esml*" buffer if the process is dead, the
    ;; buffer is missing or it's got the wrong mode.
    (unless nopop
      (pop-to-buffer buf))
    ;; create the comint process if there is no buffer.
    (unless buf-live
      (with-current-buffer buf
        (apply 'make-comint-in-buffer "inferior esml" buf
               esml-program esml-prog-arguments)
        (inf-esml-mode)))))
    ;; (with-current-buffer buf
    ;;   (setq esml-prog-proc--buffer (current-buffer)))))

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

(provide 'esml-mode)
