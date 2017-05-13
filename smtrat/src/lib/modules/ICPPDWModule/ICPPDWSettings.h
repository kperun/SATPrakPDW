/**
 * @file ICPPDWSettings.h
 * @author David
 *
 * @version 2017-04-27
 * Created on 2017-04-27.
 */

#pragma once

namespace smtrat
{
	typedef DoubleInterval IntervalT;

	struct ICPPDWSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "ICPPDWModule<ICPPDWSettings1>";

		// number of maximal contraction per ICP state
		static const int maxContractions = 10;

		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
