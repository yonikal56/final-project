; EXPECT: sat
(set-logic QF_ALL)
(set-info :status sat)
(define-sort Elt () Int)
(define-sort mySet () (Set Elt ))
(define-fun smt_set_emp () mySet (as set.empty mySet))
(define-fun smt_set_mem ((x Elt) (s mySet)) Bool (set.member x s))
(define-fun smt_set_add ((s mySet) (x Elt)) mySet (set.union s (set.singleton x)))
(define-fun smt_set_cup ((s1 mySet) (s2 mySet)) mySet (set.union s1 s2))
(define-fun smt_set_cap ((s1 mySet) (s2 mySet)) mySet (set.inter s1 s2))
;(define-fun smt_set_com ((s mySet)) mySet ((_ map not) s))
(define-fun smt_set_dif ((s1 mySet) (s2 mySet)) mySet (set.minus s1 s2))
;(define-fun smt_set_sub ((s1 mySet) (s2 mySet)) Bool (= smt_set_emp (smt_set_dif s1 s2)))
(define-fun smt_set_sub ((s1 mySet) (s2 mySet)) Bool (set.subset s1 s2))
(declare-fun z3v60 () Int)
(declare-fun z3v61 () Int)
(assert (distinct z3v60 z3v61))
(declare-fun z3f62 (Int) Bool)
(declare-fun z3v63 () Int)
(declare-fun z3f64 (Int) Int)
(declare-fun z3v65 () Int)
(declare-fun z3v66 () Int)
(declare-fun z3v69 () mySet)
(declare-fun z3v70 () mySet)
(declare-fun z3v72 () mySet)
(declare-fun z3v73 () mySet)
(declare-fun z3v75 () Int)
(declare-fun z3f76 (Int) Int)
(declare-fun z3v79 () Int)
(declare-fun z3v80 () Int)
(declare-fun z3v84 () Int)
(declare-fun z3v87 () mySet)
(declare-fun z3v88 () mySet)
(declare-fun z3v90 () mySet)
(declare-fun z3v91 () mySet)
(declare-fun z3v93 () mySet)
(declare-fun z3v94 () mySet)
(declare-fun z3v96 () Int)
(declare-fun z3f97 (Int) mySet)
(declare-fun z3f98 (Int) Bool)
(declare-fun z3v99 () Int)
(declare-fun z3v102 () Int)
(declare-fun z3v105 () mySet)
(declare-fun z3v107 () mySet)
(declare-fun z3v108 () mySet)
(declare-fun z3v109 () Int)
(declare-fun z3v110 () Int)
(declare-fun z3v111 () Int)
(declare-fun z3v112 () Int)
(declare-fun z3v113 () mySet)
(declare-fun z3v114 () mySet)
(declare-fun z3v117 () mySet)
(declare-fun z3v118 () mySet)
(declare-fun z3v121 () mySet)
(declare-fun z3v123 () mySet)
(declare-fun z3v124 () mySet)
(declare-fun z3v126 () mySet)
(declare-fun z3v128 () Int)
(declare-fun z3v132 () Int)
(declare-fun z3v135 () mySet)
(declare-fun z3v136 () mySet)
(declare-fun z3v138 () mySet)
(declare-fun z3v140 () Int)
(declare-fun z3v143 () mySet)
(declare-fun z3v144 () mySet)
(declare-fun z3v145 () mySet)
(declare-fun z3v146 () Int)
(declare-fun z3v147 () Int)
(declare-fun z3v148 () mySet)
(declare-fun z3v149 () mySet)
(declare-fun z3v155 () mySet)
(declare-fun z3v156 () mySet)
(declare-fun z3v157 () mySet)
(declare-fun z3v160 () Int)
(declare-fun z3v161 () Int)
(declare-fun z3v162 () Int)
(declare-fun z3v163 () Int)
(declare-fun z3v164 () mySet)
(declare-fun z3v165 () mySet)
(declare-fun z3v169 () Int)
(declare-fun z3v172 () mySet)
(declare-fun z3v173 () mySet)
(declare-fun z3v175 () Int)
(declare-fun z3v176 () Int)
(declare-fun z3v177 () Int)
(declare-fun z3v178 () Int)
(declare-fun z3f179 (Int Int) Int)
(declare-fun z3v180 () Int)
(declare-fun z3v181 () Int)
(declare-fun z3f183 () Int)
(declare-fun z3v184 () Int)
(declare-fun z3v185 () Int)
(declare-fun z3v186 () Int)
(declare-fun z3v187 () Int)
(declare-fun z3v188 () Int)
(declare-fun z3v189 () Int)
(declare-fun z3v192 () Int)
(declare-fun z3v193 () Int)
(declare-fun z3v197 () Int)
(declare-fun z3v198 () mySet)
(declare-fun z3v200 () Int)
(declare-fun z3v201 () Int)
(declare-fun z3v202 () Int)
(declare-fun z3v203 () Int)
(declare-fun z3v204 () Int)
(declare-fun z3v206 () Int)
(declare-fun z3v207 () Int)
(declare-fun z3v208 () Int)
(declare-fun z3v209 () Int)
(declare-fun z3v210 () Int)
(declare-fun z3v211 () Int)
(declare-fun z3f212 (Int) Int)
(declare-fun z3f213 (Int) Int)
(declare-fun z3v214 () Int)
(declare-fun z3v215 () Int)
(declare-fun z3v217 () Int)
(declare-fun z3v218 () Int)
(declare-fun z3v219 () Int)
(declare-fun z3v220 () Int)
(declare-fun z3f221 (Int Int) Int)
(declare-fun z3v222 () Int)
(declare-fun z3v223 () Int)
(declare-fun z3v224 () Int)
(declare-fun z3v225 () Int)
(declare-fun z3v226 () Int)
(declare-fun z3v227 () Int)
(declare-fun z3v228 () Int)
(declare-fun z3v229 () Int)
(declare-fun z3v230 () Int)
(declare-fun z3v231 () Int)
(declare-fun z3v232 () Int)
(declare-fun z3v233 () Int)
(declare-fun z3v234 () Int)
(declare-fun z3v235 () Int)
(declare-fun z3v236 () Int)
(declare-fun z3v237 () Int)
(declare-fun z3v238 () Int)
(declare-fun z3v239 () Int)
(declare-fun z3v240 () Int)
(declare-fun z3v241 () Int)
(declare-fun z3v242 () Int)
(declare-fun z3v243 () Int)
(declare-fun z3v244 () Int)
(declare-fun z3v245 () Int)
(declare-fun z3v246 () Int)
(declare-fun z3v247 () Int)
(declare-fun z3v248 () Int)
(declare-fun z3v249 () Int)
(declare-fun z3v250 () Int)
(declare-fun z3v251 () Int)
(declare-fun z3v252 () Int)
(declare-fun z3v253 () Int)
(declare-fun z3v254 () Int)
(declare-fun z3v255 () Int)
(declare-fun z3v256 () Int)
(declare-fun z3v257 () Int)
(declare-fun z3v258 () Int)
(declare-fun z3v259 () Int)
(declare-fun z3v260 () Int)
(declare-fun z3v261 () Int)
(declare-fun z3v262 () Int)
(declare-fun z3v263 () Int)
(declare-fun z3v264 () Int)
(declare-fun z3v265 () Int)
(declare-fun z3v266 () Int)
(declare-fun z3v267 () Int)
(declare-fun z3v268 () Int)
(declare-fun z3v269 () Int)
(declare-fun z3v271 () Int)
(declare-fun z3v273 () Int)
(declare-fun z3v275 () Int)
(declare-fun z3v277 () Int)
(declare-fun z3v279 () Int)
(declare-fun z3v281 () Int)
(declare-fun z3v283 () Int)
(declare-fun z3v286 () Int)
(declare-fun z3v289 () Int)
(declare-fun z3v290 () Int)
(declare-fun z3v291 () Int)
(declare-fun z3v292 () mySet)
(declare-fun z3v295 () mySet)
(declare-fun z3v297 () Int)
(declare-fun z3v301 () Int)
(declare-fun z3v302 () Int)
(declare-fun z3v303 () Int)
(declare-fun z3v304 () Int)
(declare-fun z3v305 () Int)
(declare-fun z3v306 () Int)
(declare-fun z3v307 () Int)
(declare-fun z3v308 () Int)
(declare-fun z3v309 () Int)
(declare-fun z3v310 () Int)
(declare-fun z3v312 () Int)
(declare-fun z3v314 () Int)
(declare-fun z3v315 () Int)
(declare-fun z3v316 () Int)
(declare-fun z3v317 () Int)
(declare-fun z3v318 () Int)
(declare-fun z3v319 () Int)
(declare-fun z3v320 () Int)
(declare-fun z3v321 () Int)
(declare-fun z3v322 () Int)
(declare-fun z3v324 () Int)
(declare-fun z3v327 () Int)
(declare-fun z3v328 () Int)
(declare-fun z3v329 () Int)
(declare-fun z3v330 () Int)
(declare-fun z3v331 () Int)
(declare-fun z3v332 () Int)
(declare-fun z3v333 () Int)
(declare-fun z3v334 () Int)
(declare-fun z3v335 () Int)
(declare-fun z3v336 () Int)
(declare-fun z3v337 () Int)
(declare-fun z3v338 () Int)
(declare-fun z3v339 () Int)
(declare-fun z3v340 () Int)
(declare-fun z3v341 () Int)
(declare-fun z3v342 () Int)
(declare-fun z3v343 () Int)
(declare-fun z3v345 () Int)
(declare-fun z3v349 () Int)
(declare-fun z3v350 () Int)
(declare-fun z3v351 () Int)
(declare-fun z3v352 () Int)
(declare-fun z3v353 () Int)
(declare-fun z3v354 () Int)
(declare-fun z3v355 () Int)
(declare-fun z3v359 () Int)
(declare-fun z3v361 () Int)
(declare-fun z3v362 () Int)
(declare-fun z3v363 () Int)
(declare-fun z3v364 () Int)
(declare-fun z3v366 () Int)
(declare-fun z3v367 () Int)
(declare-fun z3v368 () Int)
(declare-fun z3v369 () Int)
(declare-fun z3v370 () Int)
(declare-fun z3v375 () Int)
(assert (= (z3f97 z3v328) (smt_set_cup (z3f97 z3v331) (z3f97 z3v375))))
(assert (= (z3f97 z3v328) (smt_set_cup (z3f97 z3v330) (z3f97 z3v375))))
(assert (= (z3f97 z3v328) (smt_set_cup (z3f97 z3v328) (z3f97 z3v375))))
(assert (= (z3f97 z3v328) (smt_set_cup (z3f97 z3v327) (z3f97 z3v375))))
(assert (= (z3f97 z3v331) (smt_set_cup (z3f97 z3v331) (z3f97 z3v375))))
(assert (= (z3f97 z3v331) (smt_set_cup (z3f97 z3v330) (z3f97 z3v375))))
(assert (= (z3f97 z3v331) (smt_set_cup (z3f97 z3v328) (z3f97 z3v375))))
(assert (= (z3f97 z3v331) (smt_set_cup (z3f97 z3v327) (z3f97 z3v375))))
(assert (= (z3f97 z3v375) (z3f97 z3v331)))
(assert (= (z3f97 z3v375) (z3f97 z3v328)))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v327) (z3f97 z3v331))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v327) (z3f97 z3v328))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v328) (z3f97 z3v331))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v328) (z3f97 z3v330))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v328) (z3f97 z3v328))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v328) (z3f97 z3v327))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v330) (z3f97 z3v331))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v330) (z3f97 z3v328))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v331) (z3f97 z3v331))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v331) (z3f97 z3v330))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v331) (z3f97 z3v328))))
(assert (= (z3f97 z3v375) (smt_set_cup (z3f97 z3v331) (z3f97 z3v327))))
(assert (smt_set_sub (z3f97 z3v375) (z3f97 z3v331)))
(assert (smt_set_sub (z3f97 z3v375) (z3f97 z3v328)))
(assert (<= z3v375 z3v331))
(assert (<= z3v375 z3v328))
(assert (= z3v375 z3v328))
(assert (>= z3v375 z3v331))
(assert (>= z3v375 z3v328))
(assert (not (= z3v375 z3v330)))
(assert (not (= z3v375 z3v327)))
(assert (<= (z3f76 z3v375) (z3f76 z3v331)))
(assert (<= (z3f76 z3v375) (z3f76 z3v328)))
(assert (>  (z3f76 z3v375) (z3f76 z3v330)))
(assert (>  (z3f76 z3v375) (z3f76 z3v327)))
(assert (>= (z3f76 z3v375) (z3f76 z3v331)))
(assert (>= (z3f76 z3v375) (z3f76 z3v330)))
(assert (>= (z3f76 z3v375) (z3f76 z3v328)))
(assert (>= (z3f76 z3v375) (z3f76 z3v327)))
(assert (= (z3f76 z3v375) (z3f76 z3v331)))
(assert (= (z3f76 z3v375) (z3f76 z3v328)))
(assert (>  (z3f76 z3v375) 0))
(assert (= z3v375 z3v331))
(assert (>= (z3f76 z3v375) 0))
(assert (and (>= (z3f76 z3v327) 0) (>= (z3f76 z3v328) 0) (= (z3f97 z3v328) (smt_set_cup (smt_set_add smt_set_emp z3v329) (z3f97 z3v330))) (= (z3f76 z3v328) (+ 1 (z3f76 z3v330))) (= (z3f98 z3v328) false) (= z3v328 (z3f179 z3v329 z3v330)) (>= (z3f76 z3v328) 0) (= z3v328 z3v331) (>= (z3f76 z3v328) 0) (>= (z3f76 z3v330) 0) (>= (z3f76 z3v331) 0) (z3f62 z3v60) (= (z3f64 z3v63) z3v63) (= (z3f64 z3v65) z3v65) (not (z3f62 z3v61)) (= (z3f64 z3v66) z3v66)))
(assert (not (= (z3f97 z3v327) (smt_set_cup (z3f97 z3v327) (z3f97 z3v375)))))
(check-sat)
