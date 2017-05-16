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
		static const int maxContractions = 20;

        // desired interval
        static constexpr double targetInterval = 2;

        //we define a big M in order to be able to compute gain in case of inf intervals
        static const int bigM = 2000;//twiche the max interval, since we have to consider an intervall [-inf,0] to be better than [1000,0]

        //gain threshold
        static constexpr double threshold = 0.2;

        //Small value
        static constexpr double epsilon = 0.001;
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
