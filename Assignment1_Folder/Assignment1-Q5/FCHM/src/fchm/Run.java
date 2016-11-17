package fchm;

import java.io.IOException;

/**
 * Example of how to use the FCHM algorithm 
 * from the source code.
 * @author Philippe Fournier-Viger, 2014
 */
public class Run {

	public static void main(String [] arg) throws IOException{
		// input file
		String input = "input";
		// output file path
		String output = "output";

		// minimum utility treshold
		int min_utility = 30;  
		// minimum bond
		double minbond = 0.5; // the minimum bond threhsold


		// Applying the HUIMiner algorithm
		AlgoFCHM algo = new AlgoFCHM();
		algo.runAlgorithm(input, output, min_utility, minbond);
		algo.printStats();
	}

}
