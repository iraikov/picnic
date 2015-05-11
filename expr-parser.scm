
;; Chicken Scheme implementation of the box routines.  Based on
;; dfa2.sc in the benchmarks code supplied with Stalin 0.11

(define-record-type box (make-box contents)
  box? (contents box-contents box-contents-set!))

(define box make-box)
(define unbox box-contents)
(define set-box! box-contents-set!)

;; Stack routines.  Based on dfa2.sc in the benchmarks code supplied
;; with Stalin 0.11

(define (make-stack)
  (box '()))

(define (stack-empty? s)
  (null? (unbox s)))

(define (stack-push! s obj)
  (set-box! s (cons obj (unbox s)))
  s)

(define (stack-pop! s)
  (let ((l (unbox s)))
    (set-box! s (cdr l))
    (car l)))

(define (stack-cut! s start end)
  (cond
   ((negative? start)
    (error 'stack-cut! "start depth must be >= 0"))
   ((negative? end)
    (error 'stack-cut! "end depth must be >= 0"))
   ((< end start)
    (error 'stack-cut! "start depth must be <= to the end depth")))
  (let ((l (unbox s)))
    (let loop ((i 0) (l l) (nl (list)))
      (if (null? l) (set-box! s (reverse nl))
	  (if (and (>= i start) (<= i end))
	      (loop (+ i 1) (cdr l) nl)
	      (loop (+ i 1) (cdr l) (cons (car l) nl))))))
  s)

(define (stack-depth s)
  (let ((l (unbox s)))
    (length l)))

(define (stack-peek s)
  (let ((l (unbox s)))
    (car l)))

(define stack->list unbox)
(define (list->stack lst)
  (and (pair? lst) (box lst)))

(define-syntax tok
  (syntax-rules ()
    ((tok loc t) (make-lexical-token (quasiquote t) loc #f))
    ((tok loc t l) (make-lexical-token (quasiquote t) loc l))))

(define (make-parse-error loc)
  (lambda (msg #!optional arg)
    (let ((loc-str (or (and loc (if (list? loc) (conc " " loc " ") (conc " (" loc ") "))) "")))
      (cond  [(not arg) (error loc-str msg)]
	     [(lexical-token? arg)
	      (picnic:error (conc "line " (source-location-line (lexical-token-source arg)) ": " msg) loc-str
		     (conc (lexical-token-category arg) 
			   (if (lexical-token-value arg) (conc " " (lexical-token-value arg)) "")))]
	     [else (picnic:error loc-str (conc msg arg))]
	     ))))


(define (make-char-lexer port errorp loc)
  (lambda ()
    (letrec ((skip-spaces
              (lambda ()
                (let loop ((c (peek-char port)))
                  (if (and (not (eof-object? c))
                           (or (char=? c #\space) (char=? c #\tab)))
                      (begin
                        (read-char port)
                        (loop (peek-char port)))))))
             (read-number
              (lambda (l e? minus?)
                (let ((c (peek-char port)))
                  (if (and (char? c) 
			   (or (char-numeric? c) (case c ((#\. #\e) c) (else #f))
			       (and e? (not minus?) (char=? c #\-))))
                      (read-number (cons (read-char port) l)
				   (or e? (char=? c #\e))
				   (or minus? (char=? c #\-)))
		      (let ((s (list->string (reverse l))))
			(let ((n (string->number s)))
			  (if (not n) (errorp "invalid numeric string: " s) n))
			  )))))
             (read-id
              (lambda (l)
                (let ((c (peek-char port)))
                  (if (and (char? c) (or (char-alphabetic? c) (char-numeric? c) (char=? c #\_)))
                      (read-id (cons (read-char port) l))
                      (string->symbol (apply string (reverse l)))))))
             (read-string
              (lambda (l)
                (let ((c (peek-char port)))
                  (cond ((and (char? c) (or (char-alphabetic? c) (char-numeric? c) 
                                            (char-whitespace? c) (char=? c #\_)))
                         (read-string (cons (read-char port) l)))
                        ((char=? c #\")
                         (begin
                           (read-char port)
                           (string->symbol (apply string (reverse l)))))
                        (else
                         (errorp "invalid string character: " c))
                        ))
                ))
             )

      ;; -- skip spaces
      (skip-spaces)
      ;; -- read the next token
      (let loop ((c (read-char port)))
        (cond
         ((eof-object? c)      '*eoi*)
         ((char=? c #\>)       '>)
         ((char=? c #\<)       '<)
         ((char=? c #\^)       '^)
         ((char=? c #\+)       '+)
         ((char=? c #\-)       (let ((k (peek-char port)))
				 (if (or (char-numeric? k) (char=? k #\.))
				     (let ((n (read-number (list c) #f #f)))
				       (tok loc NUM n)) '-)))
         ((char=? c #\*)       '*)
         ((char=? c #\/)       '/)
         ((char=? c #\=)       '=)
         ((char=? c #\?)       (tok loc QUESTION))
         ((char=? c #\:)       (tok loc COLON))
         ((char=? c #\,)       (tok loc COMMA))
         ((char=? c #\~)       (tok loc COMMA))
         ((char=? c #\()       (tok loc LPAREN))
         ((char=? c #\))       (tok loc RPAREN))
         ((or (char-numeric? c)  (char=? c #\.) (char=? c #\-))
	  (tok loc NUM (read-number (list c) #f #f)))
         ((char=? c #\")
          (read-string (list)))
         ((char-alphabetic? c)  
	  (let ((id (read-id (list c))))
	    (case id
	      ((let LET Let)       (tok loc LET))
	      ((if IF If)          (tok loc IF))
	      ((then THEN Then)    (tok loc THEN))
	      ((else ELSE Else)    (tok loc ELSE))
	      (else 
	       (tok loc ID id)))
	    ))
	 ((or (char=? c #\space) 
	      (char=? c #\tab)
	      (char=? c #\newline)
	      (char=? c #\return))
	  (loop (read-char port)))
         (else
          (errorp "illegal character: " c)
          (skip-spaces)
          (loop (read-char port))))))))

(include "expr.grm.scm")

(define (port-line port) 
  (let-values (((line _) (port-position port)))
    line))
  
(define (port-column port)
  (let-values (((_ column) (port-position port)))
    column))

(define (picnic:parse-string-expr s #!optional loc)
  (or (and (string? s) (string-null? s) '())
      (let ((port
	     (cond ((string? s)  (open-input-string s))
		   ((port? s)    s)
		   (else (error 'picnic:parse-string-expr "bad argument type: not a string or a port: " s)))))
	(expr-parser  (let ((ll (make-char-lexer port (make-parse-error loc) (make-source-location loc (port-line port) (port-column port) -1 -1))))
			(lambda ()
			  (let ((t (ll)))
			    t)))
		      (make-parse-error loc)
		      ))))

(define (make-sym-lexer lst errorp loc)
  (if (not (list? lst)) (errorp "illegal list: " lst))
  (let ((is (make-stack)))
    (stack-push! is lst)
    (lambda ()
      (if (stack-empty? is)  '*eoi*
	  (let* ((p     (stack-pop! is))
		 (x     (and (not (null? p)) (car p)))
		 (t     (if x
			    (begin (stack-push! is (cdr p))
				   (match x
					  ((or '< '> '>= '<= '^ '+ '- '* '/ '= )      x)
					  ('?           (tok loc QUESTION))
					  (':           (tok loc COLON))
					  ('~           (tok loc COMMA))
					  ((or 'let 'LET)     (tok loc LET))
					  ((or 'if 'IF)       (tok loc IF))
					  ((or 'then 'THEN)   (tok loc THEN))
					  ((or 'else 'ELSE)   (tok loc ELSE))
					  ((? string?)  (tok loc STRING x))
					  ((? number?)  (tok loc NUM x))
					  ((? symbol?)  (tok loc ID x))
					  ((? list?)    (begin 
                                                          (stack-push! is x)
                                                          (tok loc LPAREN)))
					  (else (errorp "invalid input: " x))))
			    (if (not (stack-empty? is)) (tok loc RPAREN) '*eoi*))))
	    t)))))
	    
  

(define (picnic:parse-sym-expr lst #!optional loc)
  (let ((ret (cond ((number? lst)  lst)
		   ((symbol? lst)  lst)
		   ((and (list? lst) (null? lst) '()))
		   (else (expr-parser  (make-sym-lexer lst (make-parse-error loc) (make-source-location loc 0 0 -1 -1))
				       (make-parse-error loc))))))
    ret))
    


