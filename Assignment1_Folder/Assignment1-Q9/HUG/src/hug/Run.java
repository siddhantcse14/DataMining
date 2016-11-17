package hug;

import java.io.IOException;

/**
 * Example of how to use the HUG-Miner algorithm 
 * from the source code.
 * @author Philippe Fournier-Viger, 2014
 */
public class Run {

	public static void main(String [] arg) throws IOException{
		
		String input = "input";

		int min_utility =  20; 
		
		String output = "output";
		
		// Applying the HUIMiner algorithm
		AlgoHUGMiner hugMiner = new AlgoHUGMiner();
		hugMiner.runAlgorithm(input, output, min_utility);
		hugMiner.printStats();
	}

}
