package uspan;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.URL;

/**
 * This file is for testing the USpan algorithm
 * @see Sequence
 * @see SequenceDatabase
 * @author Philippe Fournier-Viger, 2015
 */
public class Run {
	
	public static void main(String [] arg) throws IOException{
		 // the input database
		String input = "input"; 
		// the path for saving the patterns found
		String output = "output";

		// the minimum utility threshold
		int minutil = 35;

		AlgoUSpan algo = new AlgoUSpan();
		
		// set the maximum pattern length (optional)
		algo.setMaxPatternLength(4);
		
		// run the algorithm
		algo.runAlgorithm(input, output, minutil);

		
		// print statistics
		algo.printStatistics();
	}
}
