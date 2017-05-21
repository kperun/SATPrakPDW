/**
 * @file ICPPDWSettings.h
 * @author David
 *
 * @version 2017-04-27
 * Created on 2017-04-27.
 */

#pragma once

#include "../../Common.h"
#include <experimental/optional>

namespace smtrat
{
	typedef DoubleInterval IntervalT;

	//Typedef for one or two things
	template <class T>
	using OneOrTwo = std::pair<T,std::experimental::optional<T>>;

	struct ICPPDWSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "ICPPDWModule<ICPPDWSettings1>";

		// number of maximal contraction per ICP state
		static constexpr int maxContractions = 30;

        // desired interval
        static constexpr double targetInterval = 1;

        // maximal number of splits allowed
        static constexpr int maxSplitNumber = 1;

        //we define a big M in order to be able to compute gain in case of inf intervals
        static constexpr int bigM = 2000; //twice the max interval, since we have to consider an intervall [-inf,0] to be better than [1000,0]

        //gain threshold
        static constexpr double threshold = 0.01;

        //Small value
        static constexpr double epsilon = 0.001;
	};
}
