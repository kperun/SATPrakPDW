(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |Benchmarks generated from hycomp (https://es-static.fbk.eu/tools/hycomp/). BMC instances of non-linear hybrid automata taken from: Alessandro Cimatti, Sergio Mover, Stefano Tonetta, A quantifier-free SMT encoding of non-linear hybrid automata, FMCAD 2012 and Alessandro Cimatti, Sergio Mover, Stefano Tonetta, Quantier-free encoding of invariants for Hybrid Systems, Formal Methods in System Design. This instance solves a BMC problem of depth 2 and uses the encoding obtained with quantifier elimination using qepcad encoding. Contacts: Sergio Mover (mover@fbk.eu), Stefano Tonetta (tonettas@fbk.eu), Alessandro Cimatti (cimatti@fbk.eu).|)
(set-info :category "industrial")
(set-info :status sat)
;; MathSAT API call trace
;; generated on Mon Mar 19 10:41:20 2012
(declare-fun b.counter.0__AT0 () Bool)
(declare-fun b.counter.3__AT2 () Bool)
(declare-fun b.counter.2__AT0 () Bool)
(declare-fun b.counter.1__AT0 () Bool)
(declare-fun b.counter.1__AT1 () Bool)
(declare-fun b.counter.2__AT1 () Bool)
(declare-fun speed_loss__AT0 () Real)
(declare-fun b.speed_y__AT0 () Real)
(declare-fun b.event_is_timed__AT2 () Bool)
(declare-fun b.event_is_timed__AT1 () Bool)
(declare-fun b.counter.0__AT2 () Bool)
(declare-fun b.event_is_timed__AT0 () Bool)
(declare-fun b.counter.1__AT2 () Bool)
(declare-fun b.counter.3__AT1 () Bool)
(declare-fun b.delta__AT0 () Real)
(declare-fun b.time__AT2 () Real)
(declare-fun b.y__AT1 () Real)
(declare-fun b.delta__AT2 () Real)
(declare-fun b.counter.0__AT1 () Bool)
(declare-fun b.counter.3__AT0 () Bool)
(declare-fun b.EVENT.0__AT2 () Bool)
(declare-fun b.y__AT2 () Real)
(declare-fun b.EVENT.1__AT2 () Bool)
(declare-fun b.delta__AT1 () Real)
(declare-fun b.EVENT.0__AT1 () Bool)
(declare-fun b.EVENT.1__AT0 () Bool)
(declare-fun b.EVENT.1__AT1 () Bool)
(declare-fun b.EVENT.0__AT0 () Bool)
(declare-fun b.time__AT1 () Real)
(declare-fun b.speed_y__AT1 () Real)
(declare-fun b.time__AT0 () Real)
(declare-fun b.speed_y__AT2 () Real)
(declare-fun b.y__AT0 () Real)
(declare-fun b.counter.2__AT2 () Bool)
(assert (let ((.def_399 (* 49.0 b.delta__AT2)))
(let ((.def_400 (* b.delta__AT2 .def_399)))
(let ((.def_401 (* (- 1.0) .def_400)))
(let ((.def_397 (* 10.0 b.delta__AT2)))
(let ((.def_398 (* b.speed_y__AT2 .def_397)))
(let ((.def_402 (+ .def_398 .def_401)))
(let ((.def_403 (* 10.0 b.y__AT2)))
(let ((.def_405 (+ .def_403 .def_402)))
(let ((.def_406 (<= 0.0 .def_405)))
(let ((.def_383 (<= 0.0 b.y__AT2)))
(let ((.def_407 (and .def_383 .def_406)))
(let ((.def_395 (<= 0.0 b.delta__AT2)))
(let ((.def_396 (not .def_395)))
(let ((.def_408 (or .def_396 .def_407)))
(let ((.def_380 (not b.EVENT.0__AT2)))
(let ((.def_378 (not b.EVENT.1__AT2)))
(let ((.def_392 (and .def_378 .def_380)))
(let ((.def_393 (not .def_392)))
(let ((.def_409 (or .def_393 .def_408)))
(let ((.def_110 (not b.counter.0__AT1)))
(let ((.def_98 (not b.counter.1__AT1)))
(let ((.def_387 (and .def_98 .def_110)))
(let ((.def_105 (not b.counter.2__AT1)))
(let ((.def_388 (and .def_105 .def_387)))
(let ((.def_120 (not b.counter.3__AT1)))
(let ((.def_389 (and .def_120 .def_388)))
(let ((.def_58 (<= speed_loss__AT0 (/ 1 2))))
(let ((.def_55 (<= (/ 1 10) speed_loss__AT0)))
(let ((.def_59 (and .def_55 .def_58)))
(let ((.def_384 (and .def_59 .def_383)))
(let ((.def_381 (or .def_378 .def_380)))
(let ((.def_6 (not b.counter.0__AT2)))
(let ((.def_4 (not b.counter.1__AT2)))
(let ((.def_371 (or .def_4 .def_6)))
(let ((.def_375 (or b.counter.3__AT2 .def_371)))
(let ((.def_372 (or b.counter.2__AT2 .def_371)))
(let ((.def_9 (not b.counter.2__AT2)))
(let ((.def_370 (or .def_6 .def_9)))
(let ((.def_373 (and .def_370 .def_372)))
(let ((.def_12 (not b.counter.3__AT2)))
(let ((.def_374 (or .def_12 .def_373)))
(let ((.def_376 (and .def_374 .def_375)))
(let ((.def_382 (and .def_376 .def_381)))
(let ((.def_385 (and .def_382 .def_384)))
(let ((.def_238 (<= 0.0 b.delta__AT1)))
(let ((.def_226 (not b.EVENT.0__AT1)))
(let ((.def_224 (not b.EVENT.1__AT1)))
(let ((.def_235 (and .def_224 .def_226)))
(let ((.def_236 (not .def_235)))
(let ((.def_366 (or .def_236 .def_238)))
(let ((.def_367 (or b.EVENT.1__AT1 .def_366)))
(let ((.def_300 (= b.counter.0__AT2 b.counter.0__AT1)))
(let ((.def_298 (= b.counter.1__AT2 b.counter.1__AT1)))
(let ((.def_296 (= b.counter.2__AT2 b.counter.2__AT1)))
(let ((.def_295 (= b.counter.3__AT2 b.counter.3__AT1)))
(let ((.def_297 (and .def_295 .def_296)))
(let ((.def_299 (and .def_297 .def_298)))
(let ((.def_301 (and .def_299 .def_300)))
(let ((.def_363 (or .def_236 .def_301)))
(let ((.def_364 (or b.EVENT.1__AT1 .def_363)))
(let ((.def_351 (* (- 5.0) b.speed_y__AT2)))
(let ((.def_352 (* (- 49.0) b.delta__AT1)))
(let ((.def_356 (+ .def_352 .def_351)))
(let ((.def_354 (* 5.0 b.speed_y__AT1)))
(let ((.def_357 (+ .def_354 .def_356)))
(let ((.def_358 (= .def_357 0.0 )))
(let ((.def_342 (* b.speed_y__AT1 b.delta__AT1)))
(let ((.def_343 (* 10.0 .def_342)))
(let ((.def_340 (* b.delta__AT1 b.delta__AT1)))
(let ((.def_341 (* (- 49.0) .def_340)))
(let ((.def_344 (+ .def_341 .def_343)))
(let ((.def_345 (* (- 10.0) b.y__AT2)))
(let ((.def_348 (+ .def_345 .def_344)))
(let ((.def_246 (* 10.0 b.y__AT1)))
(let ((.def_349 (+ .def_246 .def_348)))
(let ((.def_350 (= .def_349 0.0 )))
(let ((.def_359 (and .def_350 .def_358)))
(let ((.def_360 (or .def_236 .def_359)))
(let ((.def_306 (= b.y__AT1 b.y__AT2)))
(let ((.def_294 (= b.speed_y__AT1 b.speed_y__AT2)))
(let ((.def_337 (and .def_294 .def_306)))
(let ((.def_334 (= b.delta__AT1 0.0 )))
(let ((.def_335 (and .def_235 .def_334)))
(let ((.def_336 (not .def_335)))
(let ((.def_338 (or .def_336 .def_337)))
(let ((.def_339 (or b.EVENT.1__AT1 .def_338)))
(let ((.def_361 (and .def_339 .def_360)))
(let ((.def_316 (= b.time__AT1 b.time__AT2)))
(let ((.def_328 (and .def_306 .def_316)))
(let ((.def_329 (and .def_294 .def_328)))
(let ((.def_330 (and .def_301 .def_329)))
(let ((.def_331 (or .def_224 .def_330)))
(let ((.def_319 (* (- 1.0) b.time__AT2)))
(let ((.def_322 (+ b.delta__AT1 .def_319)))
(let ((.def_323 (+ b.time__AT1 .def_322)))
(let ((.def_324 (= .def_323 0.0 )))
(let ((.def_325 (or .def_236 .def_324)))
(let ((.def_326 (or b.EVENT.1__AT1 .def_325)))
(let ((.def_317 (or .def_235 .def_316)))
(let ((.def_318 (or b.EVENT.1__AT1 .def_317)))
(let ((.def_327 (and .def_318 .def_326)))
(let ((.def_332 (and .def_327 .def_331)))
(let ((.def_312 (= .def_236 b.event_is_timed__AT2)))
(let ((.def_310 (= b.event_is_timed__AT1 .def_235)))
(let ((.def_313 (and .def_310 .def_312)))
(let ((.def_302 (and .def_294 .def_301)))
(let ((.def_255 (<= 0.0 b.speed_y__AT1)))
(let ((.def_256 (not .def_255)))
(let ((.def_254 (= b.y__AT1 0.0 )))
(let ((.def_257 (and .def_254 .def_256)))
(let ((.def_303 (or .def_257 .def_302)))
(let ((.def_271 (or .def_6 b.counter.0__AT1)))
(let ((.def_270 (or b.counter.0__AT2 .def_110)))
(let ((.def_272 (and .def_270 .def_271)))
(let ((.def_273 (and .def_4 .def_272)))
(let ((.def_274 (or b.counter.1__AT1 .def_273)))
(let ((.def_269 (or b.counter.1__AT2 .def_98)))
(let ((.def_275 (and .def_269 .def_274)))
(let ((.def_286 (and .def_9 .def_275)))
(let ((.def_287 (or b.counter.2__AT1 .def_286)))
(let ((.def_281 (and .def_4 .def_110)))
(let ((.def_282 (or b.counter.1__AT1 .def_281)))
(let ((.def_283 (and .def_269 .def_282)))
(let ((.def_284 (and b.counter.2__AT2 .def_283)))
(let ((.def_285 (or .def_105 .def_284)))
(let ((.def_288 (and .def_285 .def_287)))
(let ((.def_289 (and b.counter.3__AT2 .def_288)))
(let ((.def_290 (or b.counter.3__AT1 .def_289)))
(let ((.def_276 (and b.counter.2__AT2 .def_275)))
(let ((.def_277 (or b.counter.2__AT1 .def_276)))
(let ((.def_265 (or b.counter.1__AT2 b.counter.1__AT1)))
(let ((.def_263 (and .def_4 b.counter.0__AT2)))
(let ((.def_264 (or .def_98 .def_263)))
(let ((.def_266 (and .def_264 .def_265)))
(let ((.def_267 (and .def_9 .def_266)))
(let ((.def_268 (or .def_105 .def_267)))
(let ((.def_278 (and .def_268 .def_277)))
(let ((.def_279 (and .def_12 .def_278)))
(let ((.def_280 (or .def_120 .def_279)))
(let ((.def_291 (and .def_280 .def_290)))
(let ((.def_259 (* (- 1.0) b.speed_y__AT1)))
(let ((.def_92 (* (- 1.0) speed_loss__AT0)))
(let ((.def_93 (+ 1.0 .def_92)))
(let ((.def_260 (* .def_93 .def_259)))
(let ((.def_262 (= .def_260 b.speed_y__AT2)))
(let ((.def_292 (and .def_262 .def_291)))
(let ((.def_258 (not .def_257)))
(let ((.def_293 (or .def_258 .def_292)))
(let ((.def_304 (and .def_293 .def_303)))
(let ((.def_307 (and .def_304 .def_306)))
(let ((.def_308 (or .def_235 .def_307)))
(let ((.def_309 (or b.EVENT.1__AT1 .def_308)))
(let ((.def_314 (and .def_309 .def_313)))
(let ((.def_333 (and .def_314 .def_332)))
(let ((.def_362 (and .def_333 .def_361)))
(let ((.def_365 (and .def_362 .def_364)))
(let ((.def_368 (and .def_365 .def_367)))
(let ((.def_369 (and .def_224 .def_368)))
(let ((.def_386 (and .def_369 .def_385)))
(let ((.def_390 (and .def_386 .def_389)))
(let ((.def_242 (* 49.0 b.delta__AT1)))
(let ((.def_243 (* b.delta__AT1 .def_242)))
(let ((.def_244 (* (- 1.0) .def_243)))
(let ((.def_240 (* 10.0 b.delta__AT1)))
(let ((.def_241 (* b.speed_y__AT1 .def_240)))
(let ((.def_245 (+ .def_241 .def_244)))
(let ((.def_248 (+ .def_246 .def_245)))
(let ((.def_249 (<= 0.0 .def_248)))
(let ((.def_229 (<= 0.0 b.y__AT1)))
(let ((.def_250 (and .def_229 .def_249)))
(let ((.def_239 (not .def_238)))
(let ((.def_251 (or .def_239 .def_250)))
(let ((.def_252 (or .def_236 .def_251)))
(let ((.def_230 (and .def_59 .def_229)))
(let ((.def_227 (or .def_224 .def_226)))
(let ((.def_217 (or .def_98 .def_110)))
(let ((.def_221 (or b.counter.3__AT1 .def_217)))
(let ((.def_218 (or b.counter.2__AT1 .def_217)))
(let ((.def_216 (or .def_105 .def_110)))
(let ((.def_219 (and .def_216 .def_218)))
(let ((.def_220 (or .def_120 .def_219)))
(let ((.def_222 (and .def_220 .def_221)))
(let ((.def_228 (and .def_222 .def_227)))
(let ((.def_231 (and .def_228 .def_230)))
(let ((.def_68 (<= 0.0 b.delta__AT0)))
(let ((.def_49 (not b.EVENT.0__AT0)))
(let ((.def_47 (not b.EVENT.1__AT0)))
(let ((.def_65 (and .def_47 .def_49)))
(let ((.def_66 (not .def_65)))
(let ((.def_212 (or .def_66 .def_68)))
(let ((.def_213 (or b.EVENT.1__AT0 .def_212)))
(let ((.def_142 (= b.counter.0__AT0 b.counter.0__AT1)))
(let ((.def_140 (= b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_138 (= b.counter.2__AT0 b.counter.2__AT1)))
(let ((.def_137 (= b.counter.3__AT0 b.counter.3__AT1)))
(let ((.def_139 (and .def_137 .def_138)))
(let ((.def_141 (and .def_139 .def_140)))
(let ((.def_143 (and .def_141 .def_142)))
(let ((.def_209 (or .def_66 .def_143)))
(let ((.def_210 (or b.EVENT.1__AT0 .def_209)))
(let ((.def_197 (* (- 5.0) b.speed_y__AT1)))
(let ((.def_198 (* (- 49.0) b.delta__AT0)))
(let ((.def_202 (+ .def_198 .def_197)))
(let ((.def_200 (* 5.0 b.speed_y__AT0)))
(let ((.def_203 (+ .def_200 .def_202)))
(let ((.def_204 (= .def_203 0.0 )))
(let ((.def_185 (* b.speed_y__AT0 b.delta__AT0)))
(let ((.def_186 (* 10.0 .def_185)))
(let ((.def_182 (* b.delta__AT0 b.delta__AT0)))
(let ((.def_184 (* (- 49.0) .def_182)))
(let ((.def_187 (+ .def_184 .def_186)))
(let ((.def_189 (* (- 10.0) b.y__AT1)))
(let ((.def_192 (+ .def_189 .def_187)))
(let ((.def_78 (* 10.0 b.y__AT0)))
(let ((.def_193 (+ .def_78 .def_192)))
(let ((.def_194 (= .def_193 0.0 )))
(let ((.def_205 (and .def_194 .def_204)))
(let ((.def_206 (or .def_66 .def_205)))
(let ((.def_148 (= b.y__AT0 b.y__AT1)))
(let ((.def_136 (= b.speed_y__AT0 b.speed_y__AT1)))
(let ((.def_179 (and .def_136 .def_148)))
(let ((.def_176 (= b.delta__AT0 0.0 )))
(let ((.def_177 (and .def_65 .def_176)))
(let ((.def_178 (not .def_177)))
(let ((.def_180 (or .def_178 .def_179)))
(let ((.def_181 (or b.EVENT.1__AT0 .def_180)))
(let ((.def_207 (and .def_181 .def_206)))
(let ((.def_158 (= b.time__AT0 b.time__AT1)))
(let ((.def_170 (and .def_148 .def_158)))
(let ((.def_171 (and .def_136 .def_170)))
(let ((.def_172 (and .def_143 .def_171)))
(let ((.def_173 (or .def_47 .def_172)))
(let ((.def_161 (* (- 1.0) b.time__AT1)))
(let ((.def_164 (+ b.delta__AT0 .def_161)))
(let ((.def_165 (+ b.time__AT0 .def_164)))
(let ((.def_166 (= .def_165 0.0 )))
(let ((.def_167 (or .def_66 .def_166)))
(let ((.def_168 (or b.EVENT.1__AT0 .def_167)))
(let ((.def_159 (or .def_65 .def_158)))
(let ((.def_160 (or b.EVENT.1__AT0 .def_159)))
(let ((.def_169 (and .def_160 .def_168)))
(let ((.def_174 (and .def_169 .def_173)))
(let ((.def_154 (= .def_66 b.event_is_timed__AT1)))
(let ((.def_152 (= b.event_is_timed__AT0 .def_65)))
(let ((.def_155 (and .def_152 .def_154)))
(let ((.def_144 (and .def_136 .def_143)))
(let ((.def_87 (<= 0.0 b.speed_y__AT0)))
(let ((.def_88 (not .def_87)))
(let ((.def_86 (= b.y__AT0 0.0 )))
(let ((.def_89 (and .def_86 .def_88)))
(let ((.def_145 (or .def_89 .def_144)))
(let ((.def_111 (or b.counter.0__AT0 .def_110)))
(let ((.def_30 (not b.counter.0__AT0)))
(let ((.def_109 (or .def_30 b.counter.0__AT1)))
(let ((.def_112 (and .def_109 .def_111)))
(let ((.def_113 (and .def_98 .def_112)))
(let ((.def_114 (or b.counter.1__AT0 .def_113)))
(let ((.def_28 (not b.counter.1__AT0)))
(let ((.def_108 (or .def_28 b.counter.1__AT1)))
(let ((.def_115 (and .def_108 .def_114)))
(let ((.def_128 (and .def_105 .def_115)))
(let ((.def_129 (or b.counter.2__AT0 .def_128)))
(let ((.def_123 (and .def_30 .def_98)))
(let ((.def_124 (or b.counter.1__AT0 .def_123)))
(let ((.def_125 (and .def_108 .def_124)))
(let ((.def_126 (and b.counter.2__AT1 .def_125)))
(let ((.def_33 (not b.counter.2__AT0)))
(let ((.def_127 (or .def_33 .def_126)))
(let ((.def_130 (and .def_127 .def_129)))
(let ((.def_131 (and b.counter.3__AT1 .def_130)))
(let ((.def_132 (or b.counter.3__AT0 .def_131)))
(let ((.def_116 (and b.counter.2__AT1 .def_115)))
(let ((.def_117 (or b.counter.2__AT0 .def_116)))
(let ((.def_102 (or b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_100 (and .def_98 b.counter.0__AT1)))
(let ((.def_101 (or .def_28 .def_100)))
(let ((.def_103 (and .def_101 .def_102)))
(let ((.def_106 (and .def_103 .def_105)))
(let ((.def_107 (or .def_33 .def_106)))
(let ((.def_118 (and .def_107 .def_117)))
(let ((.def_121 (and .def_118 .def_120)))
(let ((.def_36 (not b.counter.3__AT0)))
(let ((.def_122 (or .def_36 .def_121)))
(let ((.def_133 (and .def_122 .def_132)))
(let ((.def_91 (* (- 1.0) b.speed_y__AT0)))
(let ((.def_94 (* .def_91 .def_93)))
(let ((.def_96 (= .def_94 b.speed_y__AT1)))
(let ((.def_134 (and .def_96 .def_133)))
(let ((.def_90 (not .def_89)))
(let ((.def_135 (or .def_90 .def_134)))
(let ((.def_146 (and .def_135 .def_145)))
(let ((.def_149 (and .def_146 .def_148)))
(let ((.def_150 (or .def_65 .def_149)))
(let ((.def_151 (or b.EVENT.1__AT0 .def_150)))
(let ((.def_156 (and .def_151 .def_155)))
(let ((.def_175 (and .def_156 .def_174)))
(let ((.def_208 (and .def_175 .def_207)))
(let ((.def_211 (and .def_208 .def_210)))
(let ((.def_214 (and .def_211 .def_213)))
(let ((.def_215 (and .def_47 .def_214)))
(let ((.def_232 (and .def_215 .def_231)))
(let ((.def_31 (and .def_28 .def_30)))
(let ((.def_34 (and .def_31 .def_33)))
(let ((.def_37 (and .def_34 .def_36)))
(let ((.def_233 (and .def_37 .def_232)))
(let ((.def_73 (* 49.0 b.delta__AT0)))
(let ((.def_74 (* b.delta__AT0 .def_73)))
(let ((.def_76 (* (- 1.0) .def_74)))
(let ((.def_70 (* 10.0 b.delta__AT0)))
(let ((.def_71 (* b.speed_y__AT0 .def_70)))
(let ((.def_77 (+ .def_71 .def_76)))
(let ((.def_80 (+ .def_78 .def_77)))
(let ((.def_81 (<= 0.0 .def_80)))
(let ((.def_60 (<= 0.0 b.y__AT0)))
(let ((.def_82 (and .def_60 .def_81)))
(let ((.def_69 (not .def_68)))
(let ((.def_83 (or .def_69 .def_82)))
(let ((.def_84 (or .def_66 .def_83)))
(let ((.def_61 (and .def_59 .def_60)))
(let ((.def_50 (or .def_47 .def_49)))
(let ((.def_40 (or .def_28 .def_30)))
(let ((.def_44 (or b.counter.3__AT0 .def_40)))
(let ((.def_41 (or b.counter.2__AT0 .def_40)))
(let ((.def_39 (or .def_30 .def_33)))
(let ((.def_42 (and .def_39 .def_41)))
(let ((.def_43 (or .def_36 .def_42)))
(let ((.def_45 (and .def_43 .def_44)))
(let ((.def_51 (and .def_45 .def_50)))
(let ((.def_62 (and .def_51 .def_61)))
(let ((.def_25 (= b.speed_y__AT0 0.0 )))
(let ((.def_22 (= b.y__AT0 10.0 )))
(let ((.def_17 (= b.time__AT0 0.0 )))
(let ((.def_19 (and .def_17 b.event_is_timed__AT0)))
(let ((.def_23 (and .def_19 .def_22)))
(let ((.def_26 (and .def_23 .def_25)))
(let ((.def_38 (and .def_26 .def_37)))
(let ((.def_63 (and .def_38 .def_62)))
(let ((.def_7 (and .def_4 .def_6)))
(let ((.def_10 (and .def_7 .def_9)))
(let ((.def_13 (and .def_10 .def_12)))
(let ((.def_14 (not .def_13)))
(let ((.def_64 (and .def_14 .def_63)))
(let ((.def_85 (and .def_64 .def_84)))
(let ((.def_234 (and .def_85 .def_233)))
(let ((.def_253 (and .def_234 .def_252)))
(let ((.def_391 (and .def_253 .def_390)))
(let ((.def_410 (and .def_391 .def_409)))
.def_410))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
