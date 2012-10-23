#lang racket

(require racket/syntax)

(provide canonicalize term=?)

(module+ test (require rackunit))

;;;_* canonicalize 
;;;_ * definition
(define (canonicalize term) ;; -> canonicalized-term
  (syntax-case term (#%plain-app #%plain-lambda begin #%expression quote case-lambda)

    ((#%plain-app expr ...)
     #`(#%plain-app #,@(map canonicalize (syntax->list #'(expr ...)))))

    ((#%plain-lambda (id ...) expr)
     #`(#%plain-lambda (id ...) #,(canonicalize #'expr)))
    ((#%plain-lambda (id ... . rest-id) expr)
     #`(#%plain-lambda (id ... . rest-id) #,(canonicalize #'expr)))
    ((#%plain-lambda id expr)
     #`(#%plain-lambda id #,(canonicalize #'expr)))

    ;; eliminate multiple body terms
    ((#%plain-lambda formals expr ...)
     (canonicalize #`(#%plain-lambda formals (begin expr ...))))

    ((case-lambda (more ...) ...)
     #`(case-lambda #,@(map
			(lambda (c)
			  (with-syntax (((ignore more ...) (canonicalize c)))
			    #'(more ...)))
			(syntax->list #'((#%plain-lambda more ...) ...)))))

    ;; eliminate single term begin
    ;; flatten nested begin
    ((begin term ...)
     (syntax-case (let recurse ((terms #'(term ...)))
		    (syntax-case terms ()
		      (()
		       #'())
		      ((term more ...)
		       (syntax-case (canonicalize #'term) (begin)
			 ((begin term ...)
			  #`(term ... #,@(recurse #'(more ...))))
			 (term
			  #`(term #,@(recurse #'(more ...))))))))
	 ()
       ((term)
	#'term)
       ((term ...)
	#'(begin term ...))))

    ;; eliminate #%expression wrapper
    ((#%expression expr)
     (canonicalize #'expr))

    (id
     (identifier? #'id)
     #'id)
    
    ((quote datum)
     #'expr)
    
    (_
     (error "canonicalize: unrecognized or unimplemented fully expanded program form." term))
    ))
;;;_ * tests
(module+
 test
 (check free-identifier=? #'x (canonicalize #'x))
 (check free-identifier=? #'x (canonicalize #'(#%expression x)))
 (check free-identifier=? #'x (canonicalize #'(#%expression (#%expression x))))
 (check free-identifier=? #'x (canonicalize #'(begin x)))
 (check free-identifier=? #'x (canonicalize #'(begin (begin x))))
 ;; NOTE: check more cases once term=? is defined below.
 )
;;;_* term=?      
;;;_ * definition
(define (term=?-aux x y bindings)
  (syntax-case #`(#,x #,y) (#%plain-lambda begin #%plain-app quote case-lambda)
    (((begin expr-x ...)
      (begin expr-y ...))
     (let ((exprs-x (syntax->list #'(expr-x ...)))
	   (exprs-y (syntax->list #'(expr-y ...))))
       (and (= (length exprs-x) (length exprs-y))
	    (andmap (lambda (expr-x expr-y)
		      (term=?-aux expr-x expr-y bindings))
		    exprs-x
		    exprs-y))))

    (((#%plain-app expr-x ...)
      (#%plain-app expr-y ...))
     (term=?-aux #'(begin expr-x ...) #'(begin expr-y ...) bindings))

    (((#%plain-lambda (id-x ...) expr-x)
      (#%plain-lambda (id-y ...) expr-y))
     (and (= (length (syntax->list #'(id-x ...)))
	     (length (syntax->list #'(id-y ...)))))
     (term=?-aux
      #'expr-x
      #'expr-y
      (append (map syntax->list (syntax->list #'((id-x id-y) ...))) bindings)))

    (((#%plain-lambda id-x expr-x)
      (#%plain-lambda id-y expr-y))
     (and (identifier? #'id-x) (identifier? #'id-y))
     (term=?-aux
      #'expr-x
      #'expr-y
      (cons (list #'id-x #'id-y) bindings)))

    (((#%plain-lambda (id-x ... . rest-id-x) expr-x)
      (#%plain-lambda (id-y ... . rest-id-y) expr-y))
     (and (= (length (syntax->list #'(id-x ...)))
	     (length (syntax->list #'(id-y ...)))))
     (term=?-aux
      #'expr-x
      #'expr-y
      (append (map syntax->list (syntax->list #'((id-x id-y) ...)))
	      (cons (list #'rest-id-x #'rest-id-y)
		    bindings))))

    (((case-lambda x ...)
      (case-lambda y ...))
     (let ((cases-x (syntax->list #'(x ...)))
	   (cases-y (syntax->list #'(y ...))))
       (and (= (length cases-x) (length cases-y))
	    (andmap (lambda (x y)
		      (term=?-aux
		       #`(#%plain-lambda #,@x)
		       #`(#%plain-lambda #,@y)
		       bindings))
		    cases-x
		    cases-y))))

    ((id-x id-y)
     (and (identifier? #'id-x) (identifier? #'id-y))
     (cond ((assoc #'id-x bindings free-identifier=?)
	    => (lambda (x.y)
		 (free-identifier=? (cadr x.y) #'id-y)))
	   (else 
	    (free-identifier=? #'id-x #'id-y))))

    (((quote datum-x)
      (quote datum-y))
     ;; ISSUE: which equal?
     (equal? #'datum-x #'datum-y))

    (else
     #f)))

(define (term=? x y)
  (term=?-aux (canonicalize x) (canonicalize y) '()))
;;;_ * tests
(module+
 test
 (check term=?
	#'(#%plain-lambda (x) x)
	#'(#%plain-lambda (x) (#%expression x)))
 (check term=? #'x #'x)
 (check-false (term=? #'x #'y))
 (check term=?
	#'(#%plain-lambda (x) x)
	#'(#%plain-lambda (x) x))
 (check term=?
	#'(#%plain-lambda (x) x)
	#'(#%plain-lambda (y) y))
 (check term=?
	#'(#%plain-lambda x x)
	#'(#%plain-lambda y y))
 (check term=?
	#'(#%plain-lambda x (#%plain-lambda x x))
	#'(#%plain-lambda z (#%plain-lambda y y)))
 (check term=?
	#'(#%plain-lambda x (#%plain-lambda x x))
	#'(#%plain-lambda z (#%plain-lambda x x)))
 (check term=?
	#'(#%plain-lambda (x y z) y)
	#'(#%plain-lambda (a b c) b))
 (check term=?
	#'(#%plain-lambda (x y . z) z)
	#'(#%plain-lambda (a b . c) c))
 (check term=?
	#'(#%plain-lambda (x) y)
	#'(#%plain-lambda (x) (#%expression y)))
 (check term=?
	#'(begin (begin v (begin w x)) (begin (begin y)) z)
	#'(begin v w x y z))
 (check term=? #'(#%plain-app a b c) #'(#%plain-app a b c))
 (check-false  (term=? #'(#%plain-app a) #'(#%plain-app b)))
 (check term=? #'(#%plain-app a) #'(#%plain-app a))

 (check term=? #'(quote x) #'(quote x))
 (check term=? #'(quote 1) #'(quote 1))
 (check term=? #'(quote "hello") #'(quote "hello"))

 (check term=?
	#'(case-lambda (x x)
		       ((x y z) (#%plain-app x y z)))
	#'(case-lambda (x x)
		       ((a b c) (#%plain-app a b c))))
 )
;;;_* 
;;; Local variables:
;;; mode: scheme
;;; mode: allout
;;; End:
