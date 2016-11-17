# Data-Mining-Assignment
package ca.pfv.spmf.algorithms.frequentpatterns.hui_miner;

/* This file is copyright (c) 2008-2016 Philippe Fournier-Viger
*
* This file is part of the SPMF DATA MINING SOFTWARE
* (http://www.philippe-fournier-viger.com/spmf).
*
* SPMF is free software: you can redistribute it and/or modify it under the
* terms of the GNU General Public License as published by the Free Software
* Foundation, either version 3 of the License, or (at your option) any later
* version.
*
* SPMF is distributed in the hope that it will be useful, but WITHOUT ANY
* WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
* A PARTICULAR PURPOSE. See the GNU General Public License for more details.
* You should have received a copy of the GNU General Public License along with
* SPMF. If not, see <http://www.gnu.org/licenses/>.
*
*/


import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import ca.pfv.spmf.tools.MemoryLogger;

/**
 * This is an implementation of the "PHM" algorithm for Periodic High-Utility Itemsets Mining
 * as described in the conference paper : <br/><br/>
 *
 *  Fournier-Viger, P., Lin, C.W., Duong, Q.-H., Dam, T.-L. (2016). PHM: Mining Periodic High-Utility Itemsets.
 *   Proc. 16th Industrial Conference on Data Mining. Springer LNAI 9728, 15 pages .
 *
 * @see UtilityListPHM
 * @see Element
 * @author Philippe Fournier-Viger 2016
 */
public class LengthConstraintsPHM {

	/** the number of high-utility itemsets generated */
	public int phuiCount =0;

	/** the number of candidate high-utility itemsets */
	public int candidateCount =0;

	/** Map to remember the TWU of each item */
	Map<Integer, Long> mapItemToTWU;

	/** Map to remember the TWU, support and largest periodicity of each item */
	Map<Integer, ItemInfo> mapItemToItemInfo;

	/** writer to write the output file  */
	BufferedWriter writer = null;

	/** The eucs structure:  key: item   key: another item   value: twu */
	Map<Integer, Map<Integer, Long>> mapEUCS = null;

	/** The eucs structure:  key: item   key: another item   value: support */
	Map<Integer, Map<Integer, Long>> mapESCS = null;

	/** enable LA-prune strategy  */
	boolean ENABLE_LA_PRUNE = true;

	/** enable EUCP strategy  */
	boolean ENABLE_EUCP = true;

	/** enable ESCP strategy  */
	boolean ENABLE_ESCP = true;

	/** variable for debug mode */
	boolean DEBUG = false;

	/** buffer for storing the current itemset that is mined when performing mining
	* the idea is to always reuse the same buffer to reduce memory usage. */
	final int BUFFERS_SIZE = 200;
	private int[] itemsetBuffer = null;

	/** the database size (number of transactions */
	int databaseSize = 0;

	/** minimum periodicity threshold**/
	int minPeriodicity;

	/** maximum periodicity threshold **/
	int maxPeriodicity;

	/** maximum average periodicity threshold **/
	int minAveragePeriodicity;

	/** maximum average periodicity threshold **/
	int maxAveragePeriodicity;

	/** the gamma parameter **/
	double supportPruningThreshold = 0;

	/** the total execution time **/
	public double totalExecutionTime = 0;

	/** the maximumMemoryUsage **/
	public double maximumMemoryUsage = 0;

	// Change Mayank

	/** the maximum pattern length in terms of number of items */
	private int maximumLength = Integer.MAX_VALUE;

	/** the maximum pattern length in terms of number of items */
	private int minimumLength = 1;

	// Change Mayank

	/** this class represent an item and its utility in a transaction */
	class Pair{
		int item = 0;
		int utility = 0;
	}

	/** this class represent a single item and its support and periodicity */
	class ItemInfo{
		int support = 0;
		int largestPeriodicity = 0;
		int smallestPeriodicity = Integer.MAX_VALUE;
		int lastSeenTransaction = 0;
	}

	/**
	 * Default constructor
	 */
	public LengthConstraintsPHM() {

	}

	/**
	 * Run the algorithm
	 * @param input the input file path
	 * @param output the output file path
	 * @param minUtility the minimum utility threshold
	 * @param minPeriodicity the minimum periodicity threshold
	 * @param maxPeriodicity the maximum periodicity threshold
	 * @param minAveragePeriodicity
	 * @param maxAveragePeriodicity2
	 * @throws IOException exception if error while writing the file
	 */

	 // Change Mayank
	public void runAlgorithm(String input, String output, int minUtility, int minPeriodicity, int maxPeriodicity, int minAveragePeriodicity, int maxAveragePeriodicity, int minimumLength, int maximumLength) throws IOException {
		// Change Mayank
		// reset maximum
		MemoryLogger.getInstance().reset();

		/** the time at which the algorithm started */
		long startTimestamp = 0;

		// save the  periodicity thresholds
		this.maxPeriodicity = maxPeriodicity;
		this.minPeriodicity = minPeriodicity;
		this.minAveragePeriodicity = minAveragePeriodicity;
		this.maxAveragePeriodicity = maxAveragePeriodicity;

		// Change Mayank
		this.minimumLength = minimumLength;
		this.maximumLength = maximumLength;
		// Change Mayank

		// initialize the buffer for storing the current itemset
		itemsetBuffer = new int[BUFFERS_SIZE];

		if(ENABLE_EUCP){
			mapEUCS =  new HashMap<Integer, Map<Integer, Long>>();
		}
		if(ENABLE_ESCP){
			mapESCS =  new HashMap<Integer, Map<Integer, Long>>();
		}


		startTimestamp = System.currentTimeMillis();

		writer = new BufferedWriter(new FileWriter(output));

		//  We create a  map to store the TWU of each item
		mapItemToTWU = new HashMap<Integer, Long>();

		// We create a map to store the support of each item
		mapItemToItemInfo  = new HashMap<Integer, ItemInfo>();


		// We scan the database a first time to calculate the TWU of each item.
		BufferedReader myInput = null;
		databaseSize = 0;
		String thisLine = null;

		long sumOfTransactionLength = 0;  // for debugging

		try {
			// prepare the object for reading the file
			myInput = new BufferedReader(new InputStreamReader( new FileInputStream(new File(input))));
			// for each line (transaction) until the end of file
			while ((thisLine = myInput.readLine()) != null) {
				// if the line is  a comment, is  empty or is a
				// kind of metadata
				if (thisLine.isEmpty() == true ||
						thisLine.charAt(0) == '#' || thisLine.charAt(0) == '%'
								|| thisLine.charAt(0) == '@') {
					continue;
				}

				// increase the number of transactions
				databaseSize++;

				// split the transaction according to the : separator
				String split[] = thisLine.split(":");
				// the first part is the list of items
				String items[] = split[0].split(" ");
				// the second part is the transaction utility
				int transactionUtility = Integer.parseInt(split[1]);

				sumOfTransactionLength += items.length;

				// for each item, we add the transaction utility to its TWU
				for(int i=0; i <items.length; i++){


					// convert item to integer
					Integer item = Integer.parseInt(items[i]);
					// get the current TWU of that item
					Long twu = mapItemToTWU.get(item);
					// add the utility of the item in the current transaction to its twu
					twu = (twu == null)?
							transactionUtility : twu + transactionUtility;
					mapItemToTWU.put(item, twu);

					// we also add 1 to the support of the item
					ItemInfo itemInfo = mapItemToItemInfo.get(item);
					if(itemInfo == null){
						itemInfo = new ItemInfo();
						mapItemToItemInfo.put(item, itemInfo);
					}
					// increase support
					itemInfo.support++;


					// **** PHM ***********
					// calculate periodicity
					int periodicity = databaseSize - itemInfo.lastSeenTransaction;
					// update periodicity of this item
					if(itemInfo.largestPeriodicity < periodicity){
						itemInfo.largestPeriodicity = periodicity;
					}
					itemInfo.lastSeenTransaction = databaseSize;

//					if(item == 4){
//						System.out.println(periodicity);
//					}

					// IF IT IS not the first time that we see the item, we update
					// its minimum periodicity
					if(itemInfo.support != 1 && periodicity < itemInfo.smallestPeriodicity){
						itemInfo.smallestPeriodicity = periodicity;
					}
					// update average periodicity
//					itemInfo.averagePeriodicity = itemInfo.averagePeriodicity +  (double)periodicity;
//					System.out.println(itemInfo.averagePeriodicity);
					// **** END PHM ***********
				}

			}
		} catch (Exception e) {
			// catches exception if error while reading the input file
			e.printStackTrace();
		}finally {
			if(myInput != null){
				myInput.close();
			}
	    }

		supportPruningThreshold  = (((double)databaseSize) / ((double)maxAveragePeriodicity) ) - 1d ;



		// **** PHM ***********
		for(Entry<Integer,ItemInfo> entry: mapItemToItemInfo.entrySet()){
			ItemInfo itemInfo = entry.getValue();

			// calculate the last period
			int periodicity = databaseSize - itemInfo.lastSeenTransaction;

//			if(entry.getKey() == 4){
//				System.out.println(periodicity);
//			}
			// update periodicity of this item
			if(itemInfo.largestPeriodicity < periodicity){
				itemInfo.largestPeriodicity = periodicity;
			}

			// Important: we do not update the minimum periodicity of the item using its last period
			// as explained in the paper.
//			if(periodicity < itemInfo.smallestPeriodicity){
//				itemInfo.smallestPeriodicity = periodicity;
//			}
			// update average periodicity
//			itemInfo.averagePeriodicity += periodicity;
//			itemInfo.averagePeriodicity /= itemInfo.support;
			if(DEBUG){
				System.out.println(" item : " + entry.getKey()
//						+
