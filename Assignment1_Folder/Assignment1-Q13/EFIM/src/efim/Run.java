package efim;

import java.io.IOException;

/**
 * Example of how to run the EFIM algorithm from the source code, and save the result to an output file.
 * @author Philippe Fournier-Viger, 2015
 */
public class Run {

	public static void main(String [] arg) throws IOException{

		// the input and output file paths
		String input = "input";
		String output = "output";
		
		// the minutil threshold
		int minutil = 30; 

		// Run the EFIM algorithm
		AlgoEFIM algo = new AlgoEFIM();
		algo.runAlgorithm(minutil,  input, output, true, Integer.MAX_VALUE, true);
		// Print statistics
		algo.printStats();

		
		// if true in next line it will find only closed itemsets, otherwise, all frequent itemsets
		//===================
//		Itemsets itemsets = algo.runAlgorithm(minutil,  input, null, activateMerging, maximumNumberOfTransactions, activateSubTreeUtilityPruning);
//		//==========================
//		itemsets.printItemsets();
	}
	
}
