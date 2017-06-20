(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |Benchmarks generated from hycomp (https://es-static.fbk.eu/tools/hycomp/). BMC instances of non-linear hybrid automata taken from: Alessandro Cimatti, Sergio Mover, Stefano Tonetta, A quantifier-free SMT encoding of non-linear hybrid automata, FMCAD 2012 and Alessandro Cimatti, Sergio Mover, Stefano Tonetta, Quantier-free encoding of invariants for Hybrid Systems, Formal Methods in System Design. This instance solves a BMC problem of depth 2 and uses the encoding obtained with quantifier elimination using qepcad encoding. Contacts: Sergio Mover (mover@fbk.eu), Stefano Tonetta (tonettas@fbk.eu), Alessandro Cimatti (cimatti@fbk.eu).|)
(set-info :category "industrial")
(set-info :status unsat)
;; MathSAT API call trace
;; generated on Mon Mar 19 10:42:39 2012
(declare-fun b.counter.0__AT0 () Bool)
(declare-fun b.counter.2__AT0 () Bool)
(declare-fun b.counter.1__AT0 () Bool)
(declare-fun b.counter.1__AT1 () Bool)
(declare-fun b.counter.2__AT1 () Bool)
(declare-fun speed_loss__AT0 () Real)
(declare-fun b.speed_y__AT0 () Real)
(declare-fun b.speed_y__AT2 () Real)
(declare-fun b.event_is_timed__AT1 () Bool)
(declare-fun b.counter.0__AT2 () Bool)
(declare-fun b.counter.2__AT2 () Bool)
(declare-fun b.event_is_timed__AT0 () Bool)
(declare-fun b.counter.1__AT2 () Bool)
(declare-fun b.counter.3__AT2 () Bool)
(declare-fun b.counter.3__AT1 () Bool)
(declare-fun b.delta__AT0 () Real)
(declare-fun b.y__AT1 () Real)
(declare-fun b.counter.0__AT1 () Bool)
(declare-fun b.counter.3__AT0 () Bool)
(declare-fun b.delta__AT1 () Real)
(declare-fun b.event_is_timed__AT2 () Bool)
(declare-fun b.EVENT.0__AT1 () Bool)
(declare-fun b.EVENT.1__AT0 () Bool)
(declare-fun b.EVENT.1__AT1 () Bool)
(declare-fun b.EVENT.0__AT0 () Bool)
(declare-fun b.time__AT1 () Real)
(declare-fun b.speed_y__AT1 () Real)
(declare-fun b.time__AT0 () Real)
(declare-fun b.time__AT2 () Real)
(declare-fun b.delta__AT2 () Real)
(declare-fun b.EVENT.0__AT2 () Bool)
(declare-fun b.y__AT0 () Real)
(declare-fun b.y__AT2 () Real)
(declare-fun b.EVENT.1__AT2 () Bool)
(assert (let ((.def_397 (* 49.0 b.delta__AT2)))
(let ((.def_398 (* b.delta__AT2 .def_397)))
(let ((.def_399 (* (- 1.0) .def_398)))
(let ((.def_395 (* 10.0 b.delta__AT2)))
(let ((.def_396 (* b.speed_y__AT2 .def_395)))
(let ((.def_400 (+ .def_396 .def_399)))
(let ((.def_401 (* 10.0 b.y__AT2)))
(let ((.def_403 (+ .def_401 .def_400)))
(let ((.def_404 (<= 0.0 .def_403)))
(let ((.def_382 (<= 0.0 b.y__AT2)))
(let ((.def_405 (and .def_382 .def_404)))
(let ((.def_393 (<= 0.0 b.delta__AT2)))
(let ((.def_394 (not .def_393)))
(let ((.def_406 (or .def_394 .def_405)))
(let ((.def_379 (not b.EVENT.0__AT2)))
(let ((.def_377 (not b.EVENT.1__AT2)))
(let ((.def_390 (and .def_377 .def_379)))
(let ((.def_391 (not .def_390)))
(let ((.def_407 (or .def_391 .def_406)))
(let ((.def_107 (not b.counter.0__AT1)))
(let ((.def_95 (not b.counter.1__AT1)))
(let ((.def_386 (and .def_95 .def_107)))
(let ((.def_102 (not b.counter.2__AT1)))
(let ((.def_387 (and .def_102 .def_386)))
(let ((.def_55 (<= speed_loss__AT0 (/ 1 2))))
(let ((.def_52 (<= (/ 1 10) speed_loss__AT0)))
(let ((.def_56 (and .def_52 .def_55)))
(let ((.def_383 (and .def_56 .def_382)))
(let ((.def_380 (or .def_377 .def_379)))
(let ((.def_6 (not b.counter.0__AT2)))
(let ((.def_4 (not b.counter.1__AT2)))
(let ((.def_370 (or .def_4 .def_6)))
(let ((.def_374 (or b.counter.3__AT2 .def_370)))
(let ((.def_371 (or b.counter.2__AT2 .def_370)))
(let ((.def_9 (not b.counter.2__AT2)))
(let ((.def_369 (or .def_6 .def_9)))
(let ((.def_372 (and .def_369 .def_371)))
(let ((.def_277 (not b.counter.3__AT2)))
(let ((.def_373 (or .def_277 .def_372)))
(let ((.def_375 (and .def_373 .def_374)))
(let ((.def_381 (and .def_375 .def_380)))
(let ((.def_384 (and .def_381 .def_383)))
(let ((.def_235 (<= 0.0 b.delta__AT1)))
(let ((.def_223 (not b.EVENT.0__AT1)))
(let ((.def_221 (not b.EVENT.1__AT1)))
(let ((.def_232 (and .def_221 .def_223)))
(let ((.def_233 (not .def_232)))
(let ((.def_365 (or .def_233 .def_235)))
(let ((.def_366 (or b.EVENT.1__AT1 .def_365)))
(let ((.def_299 (= b.counter.0__AT2 b.counter.0__AT1)))
(let ((.def_297 (= b.counter.1__AT2 b.counter.1__AT1)))
(let ((.def_295 (= b.counter.2__AT2 b.counter.2__AT1)))
(let ((.def_294 (= b.counter.3__AT1 b.counter.3__AT2)))
(let ((.def_296 (and .def_294 .def_295)))
(let ((.def_298 (and .def_296 .def_297)))
(let ((.def_300 (and .def_298 .def_299)))
(let ((.def_362 (or .def_233 .def_300)))
(let ((.def_363 (or b.EVENT.1__AT1 .def_362)))
(let ((.def_350 (* (- 5.0) b.speed_y__AT2)))
(let ((.def_351 (* (- 49.0) b.delta__AT1)))
(let ((.def_355 (+ .def_351 .def_350)))
(let ((.def_353 (* 5.0 b.speed_y__AT1)))
(let ((.def_356 (+ .def_353 .def_355)))
(let ((.def_357 (= .def_356 0.0 )))
(let ((.def_341 (* b.speed_y__AT1 b.delta__AT1)))
(let ((.def_342 (* 10.0 .def_341)))
(let ((.def_339 (* b.delta__AT1 b.delta__AT1)))
(let ((.def_340 (* (- 49.0) .def_339)))
(let ((.def_343 (+ .def_340 .def_342)))
(let ((.def_344 (* (- 10.0) b.y__AT2)))
(let ((.def_347 (+ .def_344 .def_343)))
(let ((.def_243 (* 10.0 b.y__AT1)))
(let ((.def_348 (+ .def_243 .def_347)))
(let ((.def_349 (= .def_348 0.0 )))
(let ((.def_358 (and .def_349 .def_357)))
(let ((.def_359 (or .def_233 .def_358)))
(let ((.def_305 (= b.y__AT1 b.y__AT2)))
(let ((.def_293 (= b.speed_y__AT1 b.speed_y__AT2)))
(let ((.def_336 (and .def_293 .def_305)))
(let ((.def_333 (= b.delta__AT1 0.0 )))
(let ((.def_334 (and .def_232 .def_333)))
(let ((.def_335 (not .def_334)))
(let ((.def_337 (or .def_335 .def_336)))
(let ((.def_338 (or b.EVENT.1__AT1 .def_337)))
(let ((.def_360 (and .def_338 .def_359)))
(let ((.def_315 (= b.time__AT1 b.time__AT2)))
(let ((.def_327 (and .def_305 .def_315)))
(let ((.def_328 (and .def_293 .def_327)))
(let ((.def_329 (and .def_300 .def_328)))
(let ((.def_330 (or .def_221 .def_329)))
(let ((.def_318 (* (- 1.0) b.time__AT2)))
(let ((.def_321 (+ b.delta__AT1 .def_318)))
(let ((.def_322 (+ b.time__AT1 .def_321)))
(let ((.def_323 (= .def_322 0.0 )))
(let ((.def_324 (or .def_233 .def_323)))
(let ((.def_325 (or b.EVENT.1__AT1 .def_324)))
(let ((.def_316 (or .def_232 .def_315)))
(let ((.def_317 (or b.EVENT.1__AT1 .def_316)))
(let ((.def_326 (and .def_317 .def_325)))
(let ((.def_331 (and .def_326 .def_330)))
(let ((.def_311 (= .def_233 b.event_is_timed__AT2)))
(let ((.def_309 (= b.event_is_timed__AT1 .def_232)))
(let ((.def_312 (and .def_309 .def_311)))
(let ((.def_301 (and .def_293 .def_300)))
(let ((.def_252 (<= 0.0 b.speed_y__AT1)))
(let ((.def_253 (not .def_252)))
(let ((.def_251 (= b.y__AT1 0.0 )))
(let ((.def_254 (and .def_251 .def_253)))
(let ((.def_302 (or .def_254 .def_301)))
(let ((.def_268 (or .def_6 b.counter.0__AT1)))
(let ((.def_267 (or b.counter.0__AT2 .def_107)))
(let ((.def_269 (and .def_267 .def_268)))
(let ((.def_270 (and .def_4 .def_269)))
(let ((.def_271 (or b.counter.1__AT1 .def_270)))
(let ((.def_266 (or b.counter.1__AT2 .def_95)))
(let ((.def_272 (and .def_266 .def_271)))
(let ((.def_285 (and .def_9 .def_272)))
(let ((.def_286 (or b.counter.2__AT1 .def_285)))
(let ((.def_280 (and .def_4 .def_107)))
(let ((.def_281 (or b.counter.1__AT1 .def_280)))
(let ((.def_282 (and .def_266 .def_281)))
(let ((.def_283 (and b.counter.2__AT2 .def_282)))
(let ((.def_284 (or .def_102 .def_283)))
(let ((.def_287 (and .def_284 .def_286)))
(let ((.def_288 (and b.counter.3__AT2 .def_287)))
(let ((.def_289 (or b.counter.3__AT1 .def_288)))
(let ((.def_273 (and b.counter.2__AT2 .def_272)))
(let ((.def_274 (or b.counter.2__AT1 .def_273)))
(let ((.def_262 (or b.counter.1__AT2 b.counter.1__AT1)))
(let ((.def_260 (and .def_4 b.counter.0__AT2)))
(let ((.def_261 (or .def_95 .def_260)))
(let ((.def_263 (and .def_261 .def_262)))
(let ((.def_264 (and .def_9 .def_263)))
(let ((.def_265 (or .def_102 .def_264)))
(let ((.def_275 (and .def_265 .def_274)))
(let ((.def_278 (and .def_275 .def_277)))
(let ((.def_117 (not b.counter.3__AT1)))
(let ((.def_279 (or .def_117 .def_278)))
(let ((.def_290 (and .def_279 .def_289)))
(let ((.def_256 (* (- 1.0) b.speed_y__AT1)))
(let ((.def_89 (* (- 1.0) speed_loss__AT0)))
(let ((.def_90 (+ 1.0 .def_89)))
(let ((.def_257 (* .def_90 .def_256)))
(let ((.def_259 (= .def_257 b.speed_y__AT2)))
(let ((.def_291 (and .def_259 .def_290)))
(let ((.def_255 (not .def_254)))
(let ((.def_292 (or .def_255 .def_291)))
(let ((.def_303 (and .def_292 .def_302)))
(let ((.def_306 (and .def_303 .def_305)))
(let ((.def_307 (or .def_232 .def_306)))
(let ((.def_308 (or b.EVENT.1__AT1 .def_307)))
(let ((.def_313 (and .def_308 .def_312)))
(let ((.def_332 (and .def_313 .def_331)))
(let ((.def_361 (and .def_332 .def_360)))
(let ((.def_364 (and .def_361 .def_363)))
(let ((.def_367 (and .def_364 .def_366)))
(let ((.def_368 (and .def_221 .def_367)))
(let ((.def_385 (and .def_368 .def_384)))
(let ((.def_388 (and .def_385 .def_387)))
(let ((.def_239 (* 49.0 b.delta__AT1)))
(let ((.def_240 (* b.delta__AT1 .def_239)))
(let ((.def_241 (* (- 1.0) .def_240)))
(let ((.def_237 (* 10.0 b.delta__AT1)))
(let ((.def_238 (* b.speed_y__AT1 .def_237)))
(let ((.def_242 (+ .def_238 .def_241)))
(let ((.def_245 (+ .def_243 .def_242)))
(let ((.def_246 (<= 0.0 .def_245)))
(let ((.def_226 (<= 0.0 b.y__AT1)))
(let ((.def_247 (and .def_226 .def_246)))
(let ((.def_236 (not .def_235)))
(let ((.def_248 (or .def_236 .def_247)))
(let ((.def_249 (or .def_233 .def_248)))
(let ((.def_227 (and .def_56 .def_226)))
(let ((.def_224 (or .def_221 .def_223)))
(let ((.def_214 (or .def_95 .def_107)))
(let ((.def_218 (or b.counter.3__AT1 .def_214)))
(let ((.def_215 (or b.counter.2__AT1 .def_214)))
(let ((.def_213 (or .def_102 .def_107)))
(let ((.def_216 (and .def_213 .def_215)))
(let ((.def_217 (or .def_117 .def_216)))
(let ((.def_219 (and .def_217 .def_218)))
(let ((.def_225 (and .def_219 .def_224)))
(let ((.def_228 (and .def_225 .def_227)))
(let ((.def_65 (<= 0.0 b.delta__AT0)))
(let ((.def_46 (not b.EVENT.0__AT0)))
(let ((.def_44 (not b.EVENT.1__AT0)))
(let ((.def_62 (and .def_44 .def_46)))
(let ((.def_63 (not .def_62)))
(let ((.def_209 (or .def_63 .def_65)))
(let ((.def_210 (or b.EVENT.1__AT0 .def_209)))
(let ((.def_139 (= b.counter.0__AT0 b.counter.0__AT1)))
(let ((.def_137 (= b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_135 (= b.counter.2__AT0 b.counter.2__AT1)))
(let ((.def_134 (= b.counter.3__AT0 b.counter.3__AT1)))
(let ((.def_136 (and .def_134 .def_135)))
(let ((.def_138 (and .def_136 .def_137)))
(let ((.def_140 (and .def_138 .def_139)))
(let ((.def_206 (or .def_63 .def_140)))
(let ((.def_207 (or b.EVENT.1__AT0 .def_206)))
(let ((.def_194 (* (- 5.0) b.speed_y__AT1)))
(let ((.def_195 (* (- 49.0) b.delta__AT0)))
(let ((.def_199 (+ .def_195 .def_194)))
(let ((.def_197 (* 5.0 b.speed_y__AT0)))
(let ((.def_200 (+ .def_197 .def_199)))
(let ((.def_201 (= .def_200 0.0 )))
(let ((.def_182 (* b.speed_y__AT0 b.delta__AT0)))
(let ((.def_183 (* 10.0 .def_182)))
(let ((.def_179 (* b.delta__AT0 b.delta__AT0)))
(let ((.def_181 (* (- 49.0) .def_179)))
(let ((.def_184 (+ .def_181 .def_183)))
(let ((.def_186 (* (- 10.0) b.y__AT1)))
(let ((.def_189 (+ .def_186 .def_184)))
(let ((.def_75 (* 10.0 b.y__AT0)))
(let ((.def_190 (+ .def_75 .def_189)))
(let ((.def_191 (= .def_190 0.0 )))
(let ((.def_202 (and .def_191 .def_201)))
(let ((.def_203 (or .def_63 .def_202)))
(let ((.def_145 (= b.y__AT0 b.y__AT1)))
(let ((.def_133 (= b.speed_y__AT0 b.speed_y__AT1)))
(let ((.def_176 (and .def_133 .def_145)))
(let ((.def_173 (= b.delta__AT0 0.0 )))
(let ((.def_174 (and .def_62 .def_173)))
(let ((.def_175 (not .def_174)))
(let ((.def_177 (or .def_175 .def_176)))
(let ((.def_178 (or b.EVENT.1__AT0 .def_177)))
(let ((.def_204 (and .def_178 .def_203)))
(let ((.def_155 (= b.time__AT0 b.time__AT1)))
(let ((.def_167 (and .def_145 .def_155)))
(let ((.def_168 (and .def_133 .def_167)))
(let ((.def_169 (and .def_140 .def_168)))
(let ((.def_170 (or .def_44 .def_169)))
(let ((.def_158 (* (- 1.0) b.time__AT1)))
(let ((.def_161 (+ b.delta__AT0 .def_158)))
(let ((.def_162 (+ b.time__AT0 .def_161)))
(let ((.def_163 (= .def_162 0.0 )))
(let ((.def_164 (or .def_63 .def_163)))
(let ((.def_165 (or b.EVENT.1__AT0 .def_164)))
(let ((.def_156 (or .def_62 .def_155)))
(let ((.def_157 (or b.EVENT.1__AT0 .def_156)))
(let ((.def_166 (and .def_157 .def_165)))
(let ((.def_171 (and .def_166 .def_170)))
(let ((.def_151 (= .def_63 b.event_is_timed__AT1)))
(let ((.def_149 (= b.event_is_timed__AT0 .def_62)))
(let ((.def_152 (and .def_149 .def_151)))
(let ((.def_141 (and .def_133 .def_140)))
(let ((.def_84 (<= 0.0 b.speed_y__AT0)))
(let ((.def_85 (not .def_84)))
(let ((.def_83 (= b.y__AT0 0.0 )))
(let ((.def_86 (and .def_83 .def_85)))
(let ((.def_142 (or .def_86 .def_141)))
(let ((.def_108 (or b.counter.0__AT0 .def_107)))
(let ((.def_27 (not b.counter.0__AT0)))
(let ((.def_106 (or .def_27 b.counter.0__AT1)))
(let ((.def_109 (and .def_106 .def_108)))
(let ((.def_110 (and .def_95 .def_109)))
(let ((.def_111 (or b.counter.1__AT0 .def_110)))
(let ((.def_25 (not b.counter.1__AT0)))
(let ((.def_105 (or .def_25 b.counter.1__AT1)))
(let ((.def_112 (and .def_105 .def_111)))
(let ((.def_125 (and .def_102 .def_112)))
(let ((.def_126 (or b.counter.2__AT0 .def_125)))
(let ((.def_120 (and .def_27 .def_95)))
(let ((.def_121 (or b.counter.1__AT0 .def_120)))
(let ((.def_122 (and .def_105 .def_121)))
(let ((.def_123 (and b.counter.2__AT1 .def_122)))
(let ((.def_30 (not b.counter.2__AT0)))
(let ((.def_124 (or .def_30 .def_123)))
(let ((.def_127 (and .def_124 .def_126)))
(let ((.def_128 (and b.counter.3__AT1 .def_127)))
(let ((.def_129 (or b.counter.3__AT0 .def_128)))
(let ((.def_113 (and b.counter.2__AT1 .def_112)))
(let ((.def_114 (or b.counter.2__AT0 .def_113)))
(let ((.def_99 (or b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_97 (and .def_95 b.counter.0__AT1)))
(let ((.def_98 (or .def_25 .def_97)))
(let ((.def_100 (and .def_98 .def_99)))
(let ((.def_103 (and .def_100 .def_102)))
(let ((.def_104 (or .def_30 .def_103)))
(let ((.def_115 (and .def_104 .def_114)))
(let ((.def_118 (and .def_115 .def_117)))
(let ((.def_33 (not b.counter.3__AT0)))
(let ((.def_119 (or .def_33 .def_118)))
(let ((.def_130 (and .def_119 .def_129)))
(let ((.def_88 (* (- 1.0) b.speed_y__AT0)))
(let ((.def_91 (* .def_88 .def_90)))
(let ((.def_93 (= .def_91 b.speed_y__AT1)))
(let ((.def_131 (and .def_93 .def_130)))
(let ((.def_87 (not .def_86)))
(let ((.def_132 (or .def_87 .def_131)))
(let ((.def_143 (and .def_132 .def_142)))
(let ((.def_146 (and .def_143 .def_145)))
(let ((.def_147 (or .def_62 .def_146)))
(let ((.def_148 (or b.EVENT.1__AT0 .def_147)))
(let ((.def_153 (and .def_148 .def_152)))
(let ((.def_172 (and .def_153 .def_171)))
(let ((.def_205 (and .def_172 .def_204)))
(let ((.def_208 (and .def_205 .def_207)))
(let ((.def_211 (and .def_208 .def_210)))
(let ((.def_212 (and .def_44 .def_211)))
(let ((.def_229 (and .def_212 .def_228)))
(let ((.def_28 (and .def_25 .def_27)))
(let ((.def_31 (and .def_28 .def_30)))
(let ((.def_230 (and .def_31 .def_229)))
(let ((.def_70 (* 49.0 b.delta__AT0)))
(let ((.def_71 (* b.delta__AT0 .def_70)))
(let ((.def_73 (* (- 1.0) .def_71)))
(let ((.def_67 (* 10.0 b.delta__AT0)))
(let ((.def_68 (* b.speed_y__AT0 .def_67)))
(let ((.def_74 (+ .def_68 .def_73)))
(let ((.def_77 (+ .def_75 .def_74)))
(let ((.def_78 (<= 0.0 .def_77)))
(let ((.def_57 (<= 0.0 b.y__AT0)))
(let ((.def_79 (and .def_57 .def_78)))
(let ((.def_66 (not .def_65)))
(let ((.def_80 (or .def_66 .def_79)))
(let ((.def_81 (or .def_63 .def_80)))
(let ((.def_58 (and .def_56 .def_57)))
(let ((.def_47 (or .def_44 .def_46)))
(let ((.def_37 (or .def_25 .def_27)))
(let ((.def_41 (or b.counter.3__AT0 .def_37)))
(let ((.def_38 (or b.counter.2__AT0 .def_37)))
(let ((.def_36 (or .def_27 .def_30)))
(let ((.def_39 (and .def_36 .def_38)))
(let ((.def_40 (or .def_33 .def_39)))
(let ((.def_42 (and .def_40 .def_41)))
(let ((.def_48 (and .def_42 .def_47)))
(let ((.def_59 (and .def_48 .def_58)))
(let ((.def_34 (and .def_31 .def_33)))
(let ((.def_22 (= b.speed_y__AT0 0.0 )))
(let ((.def_19 (= b.y__AT0 10.0 )))
(let ((.def_14 (= b.time__AT0 0.0 )))
(let ((.def_16 (and .def_14 b.event_is_timed__AT0)))
(let ((.def_20 (and .def_16 .def_19)))
(let ((.def_23 (and .def_20 .def_22)))
(let ((.def_35 (and .def_23 .def_34)))
(let ((.def_60 (and .def_35 .def_59)))
(let ((.def_7 (and .def_4 .def_6)))
(let ((.def_10 (and .def_7 .def_9)))
(let ((.def_11 (not .def_10)))
(let ((.def_61 (and .def_11 .def_60)))
(let ((.def_82 (and .def_61 .def_81)))
(let ((.def_231 (and .def_82 .def_230)))
(let ((.def_250 (and .def_231 .def_249)))
(let ((.def_389 (and .def_250 .def_388)))
(let ((.def_408 (and .def_389 .def_407)))
.def_408))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
