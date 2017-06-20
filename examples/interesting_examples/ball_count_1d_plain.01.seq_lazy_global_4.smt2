(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |Benchmarks generated from hycomp (https://es-static.fbk.eu/tools/hycomp/). BMC instances of non-linear hybrid automata taken from: Alessandro Cimatti, Sergio Mover, Stefano Tonetta, A quantifier-free SMT encoding of non-linear hybrid automata, FMCAD 2012 and Alessandro Cimatti, Sergio Mover, Stefano Tonetta, Quantier-free encoding of invariants for Hybrid Systems, Formal Methods in System Design. This instance solves a BMC problem of depth 4 and uses the quantifier free encoding encoding. Contacts: Sergio Mover (mover@fbk.eu), Stefano Tonetta (tonettas@fbk.eu), Alessandro Cimatti (cimatti@fbk.eu).|)
(set-info :category "industrial")
(set-info :status sat)
;; MathSAT API call trace
;; generated on Mon Mar 19 10:40:59 2012
(declare-fun b.speed_y__AT2 () Real)
(declare-fun b.delta__AT1 () Real)
(declare-fun b.delta__AT3 () Real)
(declare-fun b.counter.2__AT3 () Bool)
(declare-fun b.event_is_timed__AT4 () Bool)
(declare-fun b.EVENT.0__AT1 () Bool)
(declare-fun b.EVENT.0__AT3 () Bool)
(declare-fun b.EVENT.1__AT0 () Bool)
(declare-fun b.counter.2__AT2 () Bool)
(declare-fun b.counter.3__AT3 () Bool)
(declare-fun b.time__AT4 () Real)
(declare-fun b.counter.0__AT4 () Bool)
(declare-fun b.EVENT.1__AT1 () Bool)
(declare-fun b.EVENT.1__AT3 () Bool)
(declare-fun b.EVENT.0__AT0 () Bool)
(declare-fun b.counter.3__AT2 () Bool)
(declare-fun b.delta__AT4 () Real)
(declare-fun b.time__AT1 () Real)
(declare-fun b.counter.1__AT4 () Bool)
(declare-fun b.EVENT.0__AT4 () Bool)
(declare-fun b.speed_y__AT1 () Real)
(declare-fun b.counter.2__AT4 () Bool)
(declare-fun b.speed_y__AT3 () Real)
(declare-fun b.time__AT0 () Real)
(declare-fun b.EVENT.1__AT4 () Bool)
(declare-fun b.counter.3__AT4 () Bool)
(declare-fun b.y__AT0 () Real)
(declare-fun b.speed_y__AT4 () Real)
(declare-fun b.event_is_timed__AT2 () Bool)
(declare-fun b.counter.0__AT0 () Bool)
(declare-fun b.counter.2__AT0 () Bool)
(declare-fun b.counter.1__AT0 () Bool)
(declare-fun b.counter.1__AT1 () Bool)
(declare-fun b.y__AT4 () Real)
(declare-fun b.counter.2__AT1 () Bool)
(declare-fun b.time__AT2 () Real)
(declare-fun b.delta__AT2 () Real)
(declare-fun speed_loss__AT0 () Real)
(declare-fun b.EVENT.0__AT2 () Bool)
(declare-fun b.speed_y__AT0 () Real)
(declare-fun b.y__AT2 () Real)
(declare-fun b.EVENT.1__AT2 () Bool)
(declare-fun b.event_is_timed__AT1 () Bool)
(declare-fun b.counter.0__AT2 () Bool)
(declare-fun b.event_is_timed__AT0 () Bool)
(declare-fun b.counter.1__AT2 () Bool)
(declare-fun b.event_is_timed__AT3 () Bool)
(declare-fun b.counter.3__AT1 () Bool)
(declare-fun b.delta__AT0 () Real)
(declare-fun b.y__AT1 () Real)
(declare-fun b.y__AT3 () Real)
(declare-fun b.counter.0__AT1 () Bool)
(declare-fun b.counter.0__AT3 () Bool)
(declare-fun b.counter.3__AT0 () Bool)
(declare-fun b.time__AT3 () Real)
(declare-fun b.counter.1__AT3 () Bool)
(assert (let ((.def_737 (* (- 49.0) b.delta__AT4)))
(let ((.def_738 (* 5.0 b.speed_y__AT4)))
(let ((.def_740 (+ .def_738 .def_737)))
(let ((.def_744 (<= .def_740 0.0 )))
(let ((.def_743 (<= b.speed_y__AT4 0.0 )))
(let ((.def_745 (and .def_743 .def_744)))
(let ((.def_741 (<= 0.0 .def_740)))
(let ((.def_736 (<= 0.0 b.speed_y__AT4)))
(let ((.def_742 (and .def_736 .def_741)))
(let ((.def_746 (or .def_742 .def_745)))
(let ((.def_728 (* b.speed_y__AT4 b.delta__AT4)))
(let ((.def_729 (* 10.0 .def_728)))
(let ((.def_726 (* b.delta__AT4 b.delta__AT4)))
(let ((.def_727 (* (- 49.0) .def_726)))
(let ((.def_730 (+ .def_727 .def_729)))
(let ((.def_731 (* 10.0 b.y__AT4)))
(let ((.def_733 (+ .def_731 .def_730)))
(let ((.def_734 (<= 0.0 .def_733)))
(let ((.def_716 (<= 0.0 b.y__AT4)))
(let ((.def_735 (and .def_716 .def_734)))
(let ((.def_747 (and .def_735 .def_746)))
(let ((.def_59 (<= speed_loss__AT0 (/ 1 2))))
(let ((.def_56 (<= (/ 1 10) speed_loss__AT0)))
(let ((.def_60 (and .def_56 .def_59)))
(let ((.def_748 (and .def_60 .def_747)))
(let ((.def_447 (not b.counter.0__AT3)))
(let ((.def_435 (not b.counter.1__AT3)))
(let ((.def_720 (and .def_435 .def_447)))
(let ((.def_442 (not b.counter.2__AT3)))
(let ((.def_721 (and .def_442 .def_720)))
(let ((.def_457 (not b.counter.3__AT3)))
(let ((.def_722 (and .def_457 .def_721)))
(let ((.def_717 (and .def_60 .def_716)))
(let ((.def_713 (not b.EVENT.0__AT4)))
(let ((.def_711 (not b.EVENT.1__AT4)))
(let ((.def_714 (or .def_711 .def_713)))
(let ((.def_6 (not b.counter.0__AT4)))
(let ((.def_4 (not b.counter.1__AT4)))
(let ((.def_704 (or .def_4 .def_6)))
(let ((.def_708 (or b.counter.3__AT4 .def_704)))
(let ((.def_705 (or b.counter.2__AT4 .def_704)))
(let ((.def_9 (not b.counter.2__AT4)))
(let ((.def_703 (or .def_6 .def_9)))
(let ((.def_706 (and .def_703 .def_705)))
(let ((.def_12 (not b.counter.3__AT4)))
(let ((.def_707 (or .def_12 .def_706)))
(let ((.def_709 (and .def_707 .def_708)))
(let ((.def_715 (and .def_709 .def_714)))
(let ((.def_718 (and .def_715 .def_717)))
(let ((.def_698 (<= 0.0 b.delta__AT3)))
(let ((.def_555 (not b.EVENT.0__AT3)))
(let ((.def_553 (not b.EVENT.1__AT3)))
(let ((.def_645 (and .def_553 .def_555)))
(let ((.def_649 (not .def_645)))
(let ((.def_699 (or .def_649 .def_698)))
(let ((.def_700 (or b.EVENT.1__AT3 .def_699)))
(let ((.def_637 (= b.counter.0__AT4 b.counter.0__AT3)))
(let ((.def_635 (= b.counter.1__AT4 b.counter.1__AT3)))
(let ((.def_633 (= b.counter.2__AT4 b.counter.2__AT3)))
(let ((.def_632 (= b.counter.3__AT4 b.counter.3__AT3)))
(let ((.def_634 (and .def_632 .def_633)))
(let ((.def_636 (and .def_634 .def_635)))
(let ((.def_638 (and .def_636 .def_637)))
(let ((.def_695 (or .def_638 .def_649)))
(let ((.def_696 (or b.EVENT.1__AT3 .def_695)))
(let ((.def_683 (* (- 10.0) b.y__AT4)))
(let ((.def_570 (* b.speed_y__AT3 b.delta__AT3)))
(let ((.def_571 (* 10.0 .def_570)))
(let ((.def_687 (+ .def_571 .def_683)))
(let ((.def_568 (* b.delta__AT3 b.delta__AT3)))
(let ((.def_569 (* (- 49.0) .def_568)))
(let ((.def_688 (+ .def_569 .def_687)))
(let ((.def_573 (* 10.0 b.y__AT3)))
(let ((.def_689 (+ .def_573 .def_688)))
(let ((.def_690 (= .def_689 0.0 )))
(let ((.def_679 (* (- 5.0) b.speed_y__AT4)))
(let ((.def_579 (* (- 49.0) b.delta__AT3)))
(let ((.def_680 (+ .def_579 .def_679)))
(let ((.def_580 (* 5.0 b.speed_y__AT3)))
(let ((.def_681 (+ .def_580 .def_680)))
(let ((.def_682 (= .def_681 0.0 )))
(let ((.def_691 (and .def_682 .def_690)))
(let ((.def_692 (or .def_649 .def_691)))
(let ((.def_643 (= b.y__AT3 b.y__AT4)))
(let ((.def_631 (= b.speed_y__AT3 b.speed_y__AT4)))
(let ((.def_676 (and .def_631 .def_643)))
(let ((.def_673 (= b.delta__AT3 0.0 )))
(let ((.def_674 (and .def_645 .def_673)))
(let ((.def_675 (not .def_674)))
(let ((.def_677 (or .def_675 .def_676)))
(let ((.def_678 (or b.EVENT.1__AT3 .def_677)))
(let ((.def_693 (and .def_678 .def_692)))
(let ((.def_655 (= b.time__AT3 b.time__AT4)))
(let ((.def_667 (and .def_643 .def_655)))
(let ((.def_668 (and .def_631 .def_667)))
(let ((.def_669 (and .def_638 .def_668)))
(let ((.def_670 (or .def_553 .def_669)))
(let ((.def_658 (* (- 1.0) b.time__AT4)))
(let ((.def_661 (+ b.delta__AT3 .def_658)))
(let ((.def_662 (+ b.time__AT3 .def_661)))
(let ((.def_663 (= .def_662 0.0 )))
(let ((.def_664 (or .def_649 .def_663)))
(let ((.def_665 (or b.EVENT.1__AT3 .def_664)))
(let ((.def_656 (or .def_645 .def_655)))
(let ((.def_657 (or b.EVENT.1__AT3 .def_656)))
(let ((.def_666 (and .def_657 .def_665)))
(let ((.def_671 (and .def_666 .def_670)))
(let ((.def_651 (= .def_649 b.event_is_timed__AT4)))
(let ((.def_648 (= b.event_is_timed__AT3 .def_645)))
(let ((.def_652 (and .def_648 .def_651)))
(let ((.def_639 (and .def_631 .def_638)))
(let ((.def_578 (<= 0.0 b.speed_y__AT3)))
(let ((.def_593 (not .def_578)))
(let ((.def_592 (= b.y__AT3 0.0 )))
(let ((.def_594 (and .def_592 .def_593)))
(let ((.def_640 (or .def_594 .def_639)))
(let ((.def_608 (or .def_6 b.counter.0__AT3)))
(let ((.def_607 (or b.counter.0__AT4 .def_447)))
(let ((.def_609 (and .def_607 .def_608)))
(let ((.def_610 (and .def_4 .def_609)))
(let ((.def_611 (or b.counter.1__AT3 .def_610)))
(let ((.def_606 (or b.counter.1__AT4 .def_435)))
(let ((.def_612 (and .def_606 .def_611)))
(let ((.def_623 (and .def_9 .def_612)))
(let ((.def_624 (or b.counter.2__AT3 .def_623)))
(let ((.def_618 (and .def_4 .def_447)))
(let ((.def_619 (or b.counter.1__AT3 .def_618)))
(let ((.def_620 (and .def_606 .def_619)))
(let ((.def_621 (and b.counter.2__AT4 .def_620)))
(let ((.def_622 (or .def_442 .def_621)))
(let ((.def_625 (and .def_622 .def_624)))
(let ((.def_626 (and b.counter.3__AT4 .def_625)))
(let ((.def_627 (or b.counter.3__AT3 .def_626)))
(let ((.def_613 (and b.counter.2__AT4 .def_612)))
(let ((.def_614 (or b.counter.2__AT3 .def_613)))
(let ((.def_602 (or b.counter.1__AT4 b.counter.1__AT3)))
(let ((.def_600 (and .def_4 b.counter.0__AT4)))
(let ((.def_601 (or .def_435 .def_600)))
(let ((.def_603 (and .def_601 .def_602)))
(let ((.def_604 (and .def_9 .def_603)))
(let ((.def_605 (or .def_442 .def_604)))
(let ((.def_615 (and .def_605 .def_614)))
(let ((.def_616 (and .def_12 .def_615)))
(let ((.def_617 (or .def_457 .def_616)))
(let ((.def_628 (and .def_617 .def_627)))
(let ((.def_596 (* (- 1.0) b.speed_y__AT3)))
(let ((.def_98 (* (- 1.0) speed_loss__AT0)))
(let ((.def_99 (+ 1.0 .def_98)))
(let ((.def_597 (* .def_99 .def_596)))
(let ((.def_599 (= .def_597 b.speed_y__AT4)))
(let ((.def_629 (and .def_599 .def_628)))
(let ((.def_595 (not .def_594)))
(let ((.def_630 (or .def_595 .def_629)))
(let ((.def_641 (and .def_630 .def_640)))
(let ((.def_644 (and .def_641 .def_643)))
(let ((.def_646 (or .def_644 .def_645)))
(let ((.def_647 (or b.EVENT.1__AT3 .def_646)))
(let ((.def_653 (and .def_647 .def_652)))
(let ((.def_672 (and .def_653 .def_671)))
(let ((.def_694 (and .def_672 .def_693)))
(let ((.def_697 (and .def_694 .def_696)))
(let ((.def_701 (and .def_697 .def_700)))
(let ((.def_702 (and .def_553 .def_701)))
(let ((.def_719 (and .def_702 .def_718)))
(let ((.def_723 (and .def_719 .def_722)))
(let ((.def_582 (+ .def_580 .def_579)))
(let ((.def_586 (<= .def_582 0.0 )))
(let ((.def_585 (<= b.speed_y__AT3 0.0 )))
(let ((.def_587 (and .def_585 .def_586)))
(let ((.def_583 (<= 0.0 .def_582)))
(let ((.def_584 (and .def_578 .def_583)))
(let ((.def_588 (or .def_584 .def_587)))
(let ((.def_572 (+ .def_569 .def_571)))
(let ((.def_575 (+ .def_573 .def_572)))
(let ((.def_576 (<= 0.0 .def_575)))
(let ((.def_558 (<= 0.0 b.y__AT3)))
(let ((.def_577 (and .def_558 .def_576)))
(let ((.def_589 (and .def_577 .def_588)))
(let ((.def_590 (and .def_60 .def_589)))
(let ((.def_281 (not b.counter.0__AT2)))
(let ((.def_269 (not b.counter.1__AT2)))
(let ((.def_562 (and .def_269 .def_281)))
(let ((.def_276 (not b.counter.2__AT2)))
(let ((.def_563 (and .def_276 .def_562)))
(let ((.def_291 (not b.counter.3__AT2)))
(let ((.def_564 (and .def_291 .def_563)))
(let ((.def_559 (and .def_60 .def_558)))
(let ((.def_556 (or .def_553 .def_555)))
(let ((.def_546 (or .def_435 .def_447)))
(let ((.def_550 (or b.counter.3__AT3 .def_546)))
(let ((.def_547 (or b.counter.2__AT3 .def_546)))
(let ((.def_545 (or .def_442 .def_447)))
(let ((.def_548 (and .def_545 .def_547)))
(let ((.def_549 (or .def_457 .def_548)))
(let ((.def_551 (and .def_549 .def_550)))
(let ((.def_557 (and .def_551 .def_556)))
(let ((.def_560 (and .def_557 .def_559)))
(let ((.def_540 (<= 0.0 b.delta__AT2)))
(let ((.def_389 (not b.EVENT.0__AT2)))
(let ((.def_387 (not b.EVENT.1__AT2)))
(let ((.def_487 (and .def_387 .def_389)))
(let ((.def_491 (not .def_487)))
(let ((.def_541 (or .def_491 .def_540)))
(let ((.def_542 (or b.EVENT.1__AT2 .def_541)))
(let ((.def_479 (= b.counter.0__AT2 b.counter.0__AT3)))
(let ((.def_477 (= b.counter.1__AT2 b.counter.1__AT3)))
(let ((.def_475 (= b.counter.2__AT2 b.counter.2__AT3)))
(let ((.def_474 (= b.counter.3__AT2 b.counter.3__AT3)))
(let ((.def_476 (and .def_474 .def_475)))
(let ((.def_478 (and .def_476 .def_477)))
(let ((.def_480 (and .def_478 .def_479)))
(let ((.def_537 (or .def_480 .def_491)))
(let ((.def_538 (or b.EVENT.1__AT2 .def_537)))
(let ((.def_525 (* (- 10.0) b.y__AT3)))
(let ((.def_404 (* b.speed_y__AT2 b.delta__AT2)))
(let ((.def_405 (* 10.0 .def_404)))
(let ((.def_529 (+ .def_405 .def_525)))
(let ((.def_402 (* b.delta__AT2 b.delta__AT2)))
(let ((.def_403 (* (- 49.0) .def_402)))
(let ((.def_530 (+ .def_403 .def_529)))
(let ((.def_407 (* 10.0 b.y__AT2)))
(let ((.def_531 (+ .def_407 .def_530)))
(let ((.def_532 (= .def_531 0.0 )))
(let ((.def_521 (* (- 5.0) b.speed_y__AT3)))
(let ((.def_413 (* (- 49.0) b.delta__AT2)))
(let ((.def_522 (+ .def_413 .def_521)))
(let ((.def_414 (* 5.0 b.speed_y__AT2)))
(let ((.def_523 (+ .def_414 .def_522)))
(let ((.def_524 (= .def_523 0.0 )))
(let ((.def_533 (and .def_524 .def_532)))
(let ((.def_534 (or .def_491 .def_533)))
(let ((.def_485 (= b.y__AT2 b.y__AT3)))
(let ((.def_473 (= b.speed_y__AT2 b.speed_y__AT3)))
(let ((.def_518 (and .def_473 .def_485)))
(let ((.def_515 (= b.delta__AT2 0.0 )))
(let ((.def_516 (and .def_487 .def_515)))
(let ((.def_517 (not .def_516)))
(let ((.def_519 (or .def_517 .def_518)))
(let ((.def_520 (or b.EVENT.1__AT2 .def_519)))
(let ((.def_535 (and .def_520 .def_534)))
(let ((.def_497 (= b.time__AT2 b.time__AT3)))
(let ((.def_509 (and .def_485 .def_497)))
(let ((.def_510 (and .def_473 .def_509)))
(let ((.def_511 (and .def_480 .def_510)))
(let ((.def_512 (or .def_387 .def_511)))
(let ((.def_500 (* (- 1.0) b.time__AT3)))
(let ((.def_503 (+ b.delta__AT2 .def_500)))
(let ((.def_504 (+ b.time__AT2 .def_503)))
(let ((.def_505 (= .def_504 0.0 )))
(let ((.def_506 (or .def_491 .def_505)))
(let ((.def_507 (or b.EVENT.1__AT2 .def_506)))
(let ((.def_498 (or .def_487 .def_497)))
(let ((.def_499 (or b.EVENT.1__AT2 .def_498)))
(let ((.def_508 (and .def_499 .def_507)))
(let ((.def_513 (and .def_508 .def_512)))
(let ((.def_493 (= .def_491 b.event_is_timed__AT3)))
(let ((.def_490 (= b.event_is_timed__AT2 .def_487)))
(let ((.def_494 (and .def_490 .def_493)))
(let ((.def_481 (and .def_473 .def_480)))
(let ((.def_412 (<= 0.0 b.speed_y__AT2)))
(let ((.def_427 (not .def_412)))
(let ((.def_426 (= b.y__AT2 0.0 )))
(let ((.def_428 (and .def_426 .def_427)))
(let ((.def_482 (or .def_428 .def_481)))
(let ((.def_448 (or b.counter.0__AT2 .def_447)))
(let ((.def_446 (or .def_281 b.counter.0__AT3)))
(let ((.def_449 (and .def_446 .def_448)))
(let ((.def_450 (and .def_435 .def_449)))
(let ((.def_451 (or b.counter.1__AT2 .def_450)))
(let ((.def_445 (or .def_269 b.counter.1__AT3)))
(let ((.def_452 (and .def_445 .def_451)))
(let ((.def_465 (and .def_442 .def_452)))
(let ((.def_466 (or b.counter.2__AT2 .def_465)))
(let ((.def_460 (and .def_281 .def_435)))
(let ((.def_461 (or b.counter.1__AT2 .def_460)))
(let ((.def_462 (and .def_445 .def_461)))
(let ((.def_463 (and b.counter.2__AT3 .def_462)))
(let ((.def_464 (or .def_276 .def_463)))
(let ((.def_467 (and .def_464 .def_466)))
(let ((.def_468 (and b.counter.3__AT3 .def_467)))
(let ((.def_469 (or b.counter.3__AT2 .def_468)))
(let ((.def_453 (and b.counter.2__AT3 .def_452)))
(let ((.def_454 (or b.counter.2__AT2 .def_453)))
(let ((.def_439 (or b.counter.1__AT2 b.counter.1__AT3)))
(let ((.def_437 (and .def_435 b.counter.0__AT3)))
(let ((.def_438 (or .def_269 .def_437)))
(let ((.def_440 (and .def_438 .def_439)))
(let ((.def_443 (and .def_440 .def_442)))
(let ((.def_444 (or .def_276 .def_443)))
(let ((.def_455 (and .def_444 .def_454)))
(let ((.def_458 (and .def_455 .def_457)))
(let ((.def_459 (or .def_291 .def_458)))
(let ((.def_470 (and .def_459 .def_469)))
(let ((.def_430 (* (- 1.0) b.speed_y__AT2)))
(let ((.def_431 (* .def_99 .def_430)))
(let ((.def_433 (= .def_431 b.speed_y__AT3)))
(let ((.def_471 (and .def_433 .def_470)))
(let ((.def_429 (not .def_428)))
(let ((.def_472 (or .def_429 .def_471)))
(let ((.def_483 (and .def_472 .def_482)))
(let ((.def_486 (and .def_483 .def_485)))
(let ((.def_488 (or .def_486 .def_487)))
(let ((.def_489 (or b.EVENT.1__AT2 .def_488)))
(let ((.def_495 (and .def_489 .def_494)))
(let ((.def_514 (and .def_495 .def_513)))
(let ((.def_536 (and .def_514 .def_535)))
(let ((.def_539 (and .def_536 .def_538)))
(let ((.def_543 (and .def_539 .def_542)))
(let ((.def_544 (and .def_387 .def_543)))
(let ((.def_561 (and .def_544 .def_560)))
(let ((.def_565 (and .def_561 .def_564)))
(let ((.def_416 (+ .def_414 .def_413)))
(let ((.def_420 (<= .def_416 0.0 )))
(let ((.def_419 (<= b.speed_y__AT2 0.0 )))
(let ((.def_421 (and .def_419 .def_420)))
(let ((.def_417 (<= 0.0 .def_416)))
(let ((.def_418 (and .def_412 .def_417)))
(let ((.def_422 (or .def_418 .def_421)))
(let ((.def_406 (+ .def_403 .def_405)))
(let ((.def_409 (+ .def_407 .def_406)))
(let ((.def_410 (<= 0.0 .def_409)))
(let ((.def_392 (<= 0.0 b.y__AT2)))
(let ((.def_411 (and .def_392 .def_410)))
(let ((.def_423 (and .def_411 .def_422)))
(let ((.def_424 (and .def_60 .def_423)))
(let ((.def_117 (not b.counter.0__AT1)))
(let ((.def_105 (not b.counter.1__AT1)))
(let ((.def_396 (and .def_105 .def_117)))
(let ((.def_112 (not b.counter.2__AT1)))
(let ((.def_397 (and .def_112 .def_396)))
(let ((.def_127 (not b.counter.3__AT1)))
(let ((.def_398 (and .def_127 .def_397)))
(let ((.def_393 (and .def_60 .def_392)))
(let ((.def_390 (or .def_387 .def_389)))
(let ((.def_380 (or .def_269 .def_281)))
(let ((.def_384 (or b.counter.3__AT2 .def_380)))
(let ((.def_381 (or b.counter.2__AT2 .def_380)))
(let ((.def_379 (or .def_276 .def_281)))
(let ((.def_382 (and .def_379 .def_381)))
(let ((.def_383 (or .def_291 .def_382)))
(let ((.def_385 (and .def_383 .def_384)))
(let ((.def_391 (and .def_385 .def_390)))
(let ((.def_394 (and .def_391 .def_393)))
(let ((.def_374 (<= 0.0 b.delta__AT1)))
(let ((.def_226 (not b.EVENT.0__AT1)))
(let ((.def_224 (not b.EVENT.1__AT1)))
(let ((.def_321 (and .def_224 .def_226)))
(let ((.def_325 (not .def_321)))
(let ((.def_375 (or .def_325 .def_374)))
(let ((.def_376 (or b.EVENT.1__AT1 .def_375)))
(let ((.def_313 (= b.counter.0__AT1 b.counter.0__AT2)))
(let ((.def_311 (= b.counter.1__AT1 b.counter.1__AT2)))
(let ((.def_309 (= b.counter.2__AT1 b.counter.2__AT2)))
(let ((.def_308 (= b.counter.3__AT1 b.counter.3__AT2)))
(let ((.def_310 (and .def_308 .def_309)))
(let ((.def_312 (and .def_310 .def_311)))
(let ((.def_314 (and .def_312 .def_313)))
(let ((.def_371 (or .def_314 .def_325)))
(let ((.def_372 (or b.EVENT.1__AT1 .def_371)))
(let ((.def_359 (* (- 10.0) b.y__AT2)))
(let ((.def_238 (* b.speed_y__AT1 b.delta__AT1)))
(let ((.def_239 (* 10.0 .def_238)))
(let ((.def_363 (+ .def_239 .def_359)))
(let ((.def_236 (* b.delta__AT1 b.delta__AT1)))
(let ((.def_237 (* (- 49.0) .def_236)))
(let ((.def_364 (+ .def_237 .def_363)))
(let ((.def_241 (* 10.0 b.y__AT1)))
(let ((.def_365 (+ .def_241 .def_364)))
(let ((.def_366 (= .def_365 0.0 )))
(let ((.def_355 (* (- 5.0) b.speed_y__AT2)))
(let ((.def_247 (* (- 49.0) b.delta__AT1)))
(let ((.def_356 (+ .def_247 .def_355)))
(let ((.def_248 (* 5.0 b.speed_y__AT1)))
(let ((.def_357 (+ .def_248 .def_356)))
(let ((.def_358 (= .def_357 0.0 )))
(let ((.def_367 (and .def_358 .def_366)))
(let ((.def_368 (or .def_325 .def_367)))
(let ((.def_319 (= b.y__AT1 b.y__AT2)))
(let ((.def_307 (= b.speed_y__AT1 b.speed_y__AT2)))
(let ((.def_352 (and .def_307 .def_319)))
(let ((.def_349 (= b.delta__AT1 0.0 )))
(let ((.def_350 (and .def_321 .def_349)))
(let ((.def_351 (not .def_350)))
(let ((.def_353 (or .def_351 .def_352)))
(let ((.def_354 (or b.EVENT.1__AT1 .def_353)))
(let ((.def_369 (and .def_354 .def_368)))
(let ((.def_331 (= b.time__AT1 b.time__AT2)))
(let ((.def_343 (and .def_319 .def_331)))
(let ((.def_344 (and .def_307 .def_343)))
(let ((.def_345 (and .def_314 .def_344)))
(let ((.def_346 (or .def_224 .def_345)))
(let ((.def_334 (* (- 1.0) b.time__AT2)))
(let ((.def_337 (+ b.delta__AT1 .def_334)))
(let ((.def_338 (+ b.time__AT1 .def_337)))
(let ((.def_339 (= .def_338 0.0 )))
(let ((.def_340 (or .def_325 .def_339)))
(let ((.def_341 (or b.EVENT.1__AT1 .def_340)))
(let ((.def_332 (or .def_321 .def_331)))
(let ((.def_333 (or b.EVENT.1__AT1 .def_332)))
(let ((.def_342 (and .def_333 .def_341)))
(let ((.def_347 (and .def_342 .def_346)))
(let ((.def_327 (= .def_325 b.event_is_timed__AT2)))
(let ((.def_324 (= b.event_is_timed__AT1 .def_321)))
(let ((.def_328 (and .def_324 .def_327)))
(let ((.def_315 (and .def_307 .def_314)))
(let ((.def_246 (<= 0.0 b.speed_y__AT1)))
(let ((.def_261 (not .def_246)))
(let ((.def_260 (= b.y__AT1 0.0 )))
(let ((.def_262 (and .def_260 .def_261)))
(let ((.def_316 (or .def_262 .def_315)))
(let ((.def_282 (or b.counter.0__AT1 .def_281)))
(let ((.def_280 (or .def_117 b.counter.0__AT2)))
(let ((.def_283 (and .def_280 .def_282)))
(let ((.def_284 (and .def_269 .def_283)))
(let ((.def_285 (or b.counter.1__AT1 .def_284)))
(let ((.def_279 (or .def_105 b.counter.1__AT2)))
(let ((.def_286 (and .def_279 .def_285)))
(let ((.def_299 (and .def_276 .def_286)))
(let ((.def_300 (or b.counter.2__AT1 .def_299)))
(let ((.def_294 (and .def_117 .def_269)))
(let ((.def_295 (or b.counter.1__AT1 .def_294)))
(let ((.def_296 (and .def_279 .def_295)))
(let ((.def_297 (and b.counter.2__AT2 .def_296)))
(let ((.def_298 (or .def_112 .def_297)))
(let ((.def_301 (and .def_298 .def_300)))
(let ((.def_302 (and b.counter.3__AT2 .def_301)))
(let ((.def_303 (or b.counter.3__AT1 .def_302)))
(let ((.def_287 (and b.counter.2__AT2 .def_286)))
(let ((.def_288 (or b.counter.2__AT1 .def_287)))
(let ((.def_273 (or b.counter.1__AT1 b.counter.1__AT2)))
(let ((.def_271 (and .def_269 b.counter.0__AT2)))
(let ((.def_272 (or .def_105 .def_271)))
(let ((.def_274 (and .def_272 .def_273)))
(let ((.def_277 (and .def_274 .def_276)))
(let ((.def_278 (or .def_112 .def_277)))
(let ((.def_289 (and .def_278 .def_288)))
(let ((.def_292 (and .def_289 .def_291)))
(let ((.def_293 (or .def_127 .def_292)))
(let ((.def_304 (and .def_293 .def_303)))
(let ((.def_264 (* (- 1.0) b.speed_y__AT1)))
(let ((.def_265 (* .def_99 .def_264)))
(let ((.def_267 (= .def_265 b.speed_y__AT2)))
(let ((.def_305 (and .def_267 .def_304)))
(let ((.def_263 (not .def_262)))
(let ((.def_306 (or .def_263 .def_305)))
(let ((.def_317 (and .def_306 .def_316)))
(let ((.def_320 (and .def_317 .def_319)))
(let ((.def_322 (or .def_320 .def_321)))
(let ((.def_323 (or b.EVENT.1__AT1 .def_322)))
(let ((.def_329 (and .def_323 .def_328)))
(let ((.def_348 (and .def_329 .def_347)))
(let ((.def_370 (and .def_348 .def_369)))
(let ((.def_373 (and .def_370 .def_372)))
(let ((.def_377 (and .def_373 .def_376)))
(let ((.def_378 (and .def_224 .def_377)))
(let ((.def_395 (and .def_378 .def_394)))
(let ((.def_399 (and .def_395 .def_398)))
(let ((.def_250 (+ .def_248 .def_247)))
(let ((.def_254 (<= .def_250 0.0 )))
(let ((.def_253 (<= b.speed_y__AT1 0.0 )))
(let ((.def_255 (and .def_253 .def_254)))
(let ((.def_251 (<= 0.0 .def_250)))
(let ((.def_252 (and .def_246 .def_251)))
(let ((.def_256 (or .def_252 .def_255)))
(let ((.def_240 (+ .def_237 .def_239)))
(let ((.def_243 (+ .def_241 .def_240)))
(let ((.def_244 (<= 0.0 .def_243)))
(let ((.def_229 (<= 0.0 b.y__AT1)))
(let ((.def_245 (and .def_229 .def_244)))
(let ((.def_257 (and .def_245 .def_256)))
(let ((.def_258 (and .def_60 .def_257)))
(let ((.def_230 (and .def_60 .def_229)))
(let ((.def_227 (or .def_224 .def_226)))
(let ((.def_217 (or .def_105 .def_117)))
(let ((.def_221 (or b.counter.3__AT1 .def_217)))
(let ((.def_218 (or b.counter.2__AT1 .def_217)))
(let ((.def_216 (or .def_112 .def_117)))
(let ((.def_219 (and .def_216 .def_218)))
(let ((.def_220 (or .def_127 .def_219)))
(let ((.def_222 (and .def_220 .def_221)))
(let ((.def_228 (and .def_222 .def_227)))
(let ((.def_231 (and .def_228 .def_230)))
(let ((.def_211 (<= 0.0 b.delta__AT0)))
(let ((.def_49 (not b.EVENT.0__AT0)))
(let ((.def_47 (not b.EVENT.1__AT0)))
(let ((.def_157 (and .def_47 .def_49)))
(let ((.def_161 (not .def_157)))
(let ((.def_212 (or .def_161 .def_211)))
(let ((.def_213 (or b.EVENT.1__AT0 .def_212)))
(let ((.def_149 (= b.counter.0__AT0 b.counter.0__AT1)))
(let ((.def_147 (= b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_145 (= b.counter.2__AT0 b.counter.2__AT1)))
(let ((.def_144 (= b.counter.3__AT0 b.counter.3__AT1)))
(let ((.def_146 (and .def_144 .def_145)))
(let ((.def_148 (and .def_146 .def_147)))
(let ((.def_150 (and .def_148 .def_149)))
(let ((.def_208 (or .def_150 .def_161)))
(let ((.def_209 (or b.EVENT.1__AT0 .def_208)))
(let ((.def_197 (* (- 10.0) b.y__AT1)))
(let ((.def_70 (* b.speed_y__AT0 b.delta__AT0)))
(let ((.def_71 (* 10.0 .def_70)))
(let ((.def_200 (+ .def_71 .def_197)))
(let ((.def_66 (* b.delta__AT0 b.delta__AT0)))
(let ((.def_69 (* (- 49.0) .def_66)))
(let ((.def_201 (+ .def_69 .def_200)))
(let ((.def_73 (* 10.0 b.y__AT0)))
(let ((.def_202 (+ .def_73 .def_201)))
(let ((.def_203 (= .def_202 0.0 )))
(let ((.def_192 (* (- 5.0) b.speed_y__AT1)))
(let ((.def_79 (* (- 49.0) b.delta__AT0)))
(let ((.def_193 (+ .def_79 .def_192)))
(let ((.def_81 (* 5.0 b.speed_y__AT0)))
(let ((.def_194 (+ .def_81 .def_193)))
(let ((.def_195 (= .def_194 0.0 )))
(let ((.def_204 (and .def_195 .def_203)))
(let ((.def_205 (or .def_161 .def_204)))
(let ((.def_155 (= b.y__AT0 b.y__AT1)))
(let ((.def_143 (= b.speed_y__AT0 b.speed_y__AT1)))
(let ((.def_188 (and .def_143 .def_155)))
(let ((.def_185 (= b.delta__AT0 0.0 )))
(let ((.def_186 (and .def_157 .def_185)))
(let ((.def_187 (not .def_186)))
(let ((.def_189 (or .def_187 .def_188)))
(let ((.def_190 (or b.EVENT.1__AT0 .def_189)))
(let ((.def_206 (and .def_190 .def_205)))
(let ((.def_167 (= b.time__AT0 b.time__AT1)))
(let ((.def_179 (and .def_155 .def_167)))
(let ((.def_180 (and .def_143 .def_179)))
(let ((.def_181 (and .def_150 .def_180)))
(let ((.def_182 (or .def_47 .def_181)))
(let ((.def_170 (* (- 1.0) b.time__AT1)))
(let ((.def_173 (+ b.delta__AT0 .def_170)))
(let ((.def_174 (+ b.time__AT0 .def_173)))
(let ((.def_175 (= .def_174 0.0 )))
(let ((.def_176 (or .def_161 .def_175)))
(let ((.def_177 (or b.EVENT.1__AT0 .def_176)))
(let ((.def_168 (or .def_157 .def_167)))
(let ((.def_169 (or b.EVENT.1__AT0 .def_168)))
(let ((.def_178 (and .def_169 .def_177)))
(let ((.def_183 (and .def_178 .def_182)))
(let ((.def_163 (= .def_161 b.event_is_timed__AT1)))
(let ((.def_160 (= b.event_is_timed__AT0 .def_157)))
(let ((.def_164 (and .def_160 .def_163)))
(let ((.def_151 (and .def_143 .def_150)))
(let ((.def_78 (<= 0.0 b.speed_y__AT0)))
(let ((.def_94 (not .def_78)))
(let ((.def_93 (= b.y__AT0 0.0 )))
(let ((.def_95 (and .def_93 .def_94)))
(let ((.def_152 (or .def_95 .def_151)))
(let ((.def_118 (or b.counter.0__AT0 .def_117)))
(let ((.def_30 (not b.counter.0__AT0)))
(let ((.def_116 (or .def_30 b.counter.0__AT1)))
(let ((.def_119 (and .def_116 .def_118)))
(let ((.def_120 (and .def_105 .def_119)))
(let ((.def_121 (or b.counter.1__AT0 .def_120)))
(let ((.def_28 (not b.counter.1__AT0)))
(let ((.def_115 (or .def_28 b.counter.1__AT1)))
(let ((.def_122 (and .def_115 .def_121)))
(let ((.def_135 (and .def_112 .def_122)))
(let ((.def_136 (or b.counter.2__AT0 .def_135)))
(let ((.def_130 (and .def_30 .def_105)))
(let ((.def_131 (or b.counter.1__AT0 .def_130)))
(let ((.def_132 (and .def_115 .def_131)))
(let ((.def_133 (and b.counter.2__AT1 .def_132)))
(let ((.def_33 (not b.counter.2__AT0)))
(let ((.def_134 (or .def_33 .def_133)))
(let ((.def_137 (and .def_134 .def_136)))
(let ((.def_138 (and b.counter.3__AT1 .def_137)))
(let ((.def_139 (or b.counter.3__AT0 .def_138)))
(let ((.def_123 (and b.counter.2__AT1 .def_122)))
(let ((.def_124 (or b.counter.2__AT0 .def_123)))
(let ((.def_109 (or b.counter.1__AT0 b.counter.1__AT1)))
(let ((.def_107 (and .def_105 b.counter.0__AT1)))
(let ((.def_108 (or .def_28 .def_107)))
(let ((.def_110 (and .def_108 .def_109)))
(let ((.def_113 (and .def_110 .def_112)))
(let ((.def_114 (or .def_33 .def_113)))
(let ((.def_125 (and .def_114 .def_124)))
(let ((.def_128 (and .def_125 .def_127)))
(let ((.def_36 (not b.counter.3__AT0)))
(let ((.def_129 (or .def_36 .def_128)))
(let ((.def_140 (and .def_129 .def_139)))
(let ((.def_100 (* (- 1.0) b.speed_y__AT0)))
(let ((.def_101 (* .def_99 .def_100)))
(let ((.def_103 (= .def_101 b.speed_y__AT1)))
(let ((.def_141 (and .def_103 .def_140)))
(let ((.def_96 (not .def_95)))
(let ((.def_142 (or .def_96 .def_141)))
(let ((.def_153 (and .def_142 .def_152)))
(let ((.def_156 (and .def_153 .def_155)))
(let ((.def_158 (or .def_156 .def_157)))
(let ((.def_159 (or b.EVENT.1__AT0 .def_158)))
(let ((.def_165 (and .def_159 .def_164)))
(let ((.def_184 (and .def_165 .def_183)))
(let ((.def_207 (and .def_184 .def_206)))
(let ((.def_210 (and .def_207 .def_209)))
(let ((.def_214 (and .def_210 .def_213)))
(let ((.def_215 (and .def_47 .def_214)))
(let ((.def_232 (and .def_215 .def_231)))
(let ((.def_31 (and .def_28 .def_30)))
(let ((.def_34 (and .def_31 .def_33)))
(let ((.def_37 (and .def_34 .def_36)))
(let ((.def_233 (and .def_37 .def_232)))
(let ((.def_83 (+ .def_81 .def_79)))
(let ((.def_87 (<= .def_83 0.0 )))
(let ((.def_86 (<= b.speed_y__AT0 0.0 )))
(let ((.def_88 (and .def_86 .def_87)))
(let ((.def_84 (<= 0.0 .def_83)))
(let ((.def_85 (and .def_78 .def_84)))
(let ((.def_89 (or .def_85 .def_88)))
(let ((.def_72 (+ .def_69 .def_71)))
(let ((.def_75 (+ .def_73 .def_72)))
(let ((.def_76 (<= 0.0 .def_75)))
(let ((.def_52 (<= 0.0 b.y__AT0)))
(let ((.def_77 (and .def_52 .def_76)))
(let ((.def_90 (and .def_77 .def_89)))
(let ((.def_91 (and .def_60 .def_90)))
(let ((.def_61 (and .def_52 .def_60)))
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
(let ((.def_92 (and .def_64 .def_91)))
(let ((.def_234 (and .def_92 .def_233)))
(let ((.def_259 (and .def_234 .def_258)))
(let ((.def_400 (and .def_259 .def_399)))
(let ((.def_425 (and .def_400 .def_424)))
(let ((.def_566 (and .def_425 .def_565)))
(let ((.def_591 (and .def_566 .def_590)))
(let ((.def_724 (and .def_591 .def_723)))
(let ((.def_749 (and .def_724 .def_748)))
.def_749)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
