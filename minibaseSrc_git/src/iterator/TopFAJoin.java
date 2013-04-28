package iterator;

import global.AttrOperator;
import global.AttrType;
import global.ConstantVars;
import global.GlobalConst;
import global.IndexType;
import global.RID;
import global.TupleOrder;
import heap.FieldNumberOutOfBoundException;
import heap.FileAlreadyDeletedException;
import heap.HFBufMgrException;
import heap.HFDiskMgrException;
import heap.HFException;
import heap.Heapfile;
import heap.InvalidSlotNumberException;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.InvalidUpdateException;
import heap.Scan;
import heap.SpaceNotAvailableException;
import heap.Tuple;
import index.IndexException;
import index.IndexScan;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.TreeMap;

import btree.BTreeFile;
import btree.IntegerKey;
import btree.StringKey;
import bufmgr.PageNotReadException;

public class TopFAJoin extends Iterator {

	private int numberOfTables;
	private AttrType inputRelations[][];
	private int lengths[];
	private short[][] stringSizes;
	private int joinColumns[];
	private Iterator iterators[];
	private CondExpr[] outFilter;
	private int knumberOfTuples;
	private FldSpec[] proj_list;
	private Tuple innerTuples[];
	private int n_buf_pgs;
	private int numOutputFlds;
	private Tuple JTuple;
	private int numOfScanned[], numOfProbed[];
	private Heapfile heapFiles[], outFile;
	private boolean firstTime;
	private String[] indexFileNames;
	private boolean duplFlag = false;
	private String[] fileNames;
	private String[] updateFileNames;
	private String[] updateIndexNames;
	private Tuple combinedTuple = new Tuple();
	private Tuple randomTuple = new Tuple();
	private Tuple t = new Tuple();
	private RID newRid = new RID();
	private int combinedAttrCount = 0;
	private Heapfile tempFile = null;
	private FileScan fScan = null;
	private Tuple mainTuple = new Tuple();
	private AttrType[] combinedAttr = null;
	private short[] combinedStrSizes = null;
	private FldSpec[] combinedProjection = null;
	private float[] topkMinSum;
	private float topKmin = 1.0f;
	private HashMap<Integer, ArrayList<String>> ridMap = new HashMap<Integer, ArrayList<String>>();
	private HashMap<Integer, Boolean> relMap = new HashMap<Integer, Boolean>();
	private HashMap<String, ArrayList<Float>> keyMap = new HashMap<String, ArrayList<Float>>();
	private boolean checkFirst = false;
	private RID lastAccessedRID = new RID();
	private BTreeFile tempFileBtf = null;
	private BTreeFile insertIndex = null;

	public TopFAJoin(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			IndexType[] index, java.lang.String[] indNames, int amt_of_mem,
			CondExpr[] outFilter, FldSpec[] proj_list, int n_out_flds, int num,
			int rank, String[] fileNames) throws IOException,
			TopRankJoinException {

		// System.out.println("in TopFA");
		numberOfTables = numTables;
		inputRelations = new AttrType[numTables][];
		indexFileNames = indNames;
		joinColumns = join_col_in;
		outFile = null;
		iterators = am;
		this.fileNames = fileNames;
		topkMinSum = new float[numberOfTables];
		// System.out.println("iterators : "+iterators.length);
		try {
			outFile = new Heapfile("TopRankJoin.in");
		} catch (HFException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (HFBufMgrException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (HFDiskMgrException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		if (duplFlag) {

		}
		// Copy the attribute types
		lengths = new int[numTables];

		for (int i = 0; i < in.length; i++) {
			inputRelations[i] = new AttrType[in[i].length];
			lengths[i] = len_in[i];
			for (int j = 0; j < in[i].length; j++) {
				inputRelations[i][j] = in[i][j];
			}
		}

		// Copy the iterators
		iterators = new Iterator[am.length];
		for (int i = 0; i < numTables; i++) {
			iterators[i] = am[i];
		}

		innerTuples = new Tuple[numTables];

		// Copy the String sizes and initialize tuples
		stringSizes = new short[s_sizes.length][];
		// innerTuples = new
		for (int i = 0; i < numTables; i++) {
			stringSizes[i] = s_sizes[i];
			// innerTuples[i] = new Tuple();
		}

		JTuple = new Tuple();
		n_buf_pgs = amt_of_mem;
		numOutputFlds = n_out_flds;
		knumberOfTuples = num;

		AttrType[] Restypes = new AttrType[n_out_flds];

		// Copy projection list and conditions
		// Initialize scanned and probed counters
		numOfProbed = new int[numTables];
		numOfScanned = new int[numTables];
		this.outFilter = new CondExpr[outFilter.length];
		this.proj_list = new FldSpec[proj_list.length];
		for (int i = 0; i < outFilter.length; i++) {
			this.outFilter[i] = outFilter[i];
			numOfProbed[i] = 0;
			numOfScanned[i] = 0;
		}

		for (int i = 0; i < proj_list.length; i++) {
			this.proj_list[i] = proj_list[i];
		}
		// Initialize Heap Files
		try {
			heapFiles = new Heapfile[numTables];
			for (int i = 0; i < numTables; i++) {
				heapFiles[i] = new Heapfile(indNames[i]);
			}
		} catch (Exception e) {
			throw new TopRankJoinException(e, " Create new heapfile failed ");
		}
		firstTime = true;
		int strAttrCount = 0;
		try {
			tempFile = new Heapfile("TempResults.in");
		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		for (int i = 0; i < inputRelations.length; i++) {
			combinedAttrCount += inputRelations[i].length;
		}
		for (int i = 0; i < stringSizes.length; i++) {
			strAttrCount += stringSizes[i].length;
		}
		if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrString) {
			strAttrCount += 1;
		}
		combinedAttrCount += 3;
		int attrCount = 0;
		int strCount = 0;
		combinedAttr = new AttrType[combinedAttrCount];
		combinedStrSizes = new short[strAttrCount];
		for (int i = 0; i < inputRelations.length; i++) {
			int count = 0;
			for (int j = 0; j < inputRelations[i].length; j++) {
				// System.out.println("attr length: "+
				// inputRelations[i].length);
				combinedAttr[attrCount++] = inputRelations[i][j];
				if (inputRelations[i][j].attrType == AttrType.attrString)
					combinedStrSizes[strCount++] = stringSizes[i][count++];
			}
		}
		combinedAttr[attrCount++] = new AttrType(AttrType.attrReal);
		combinedAttr[attrCount++] = new AttrType(AttrType.attrInteger);
		if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrInteger) {
			combinedAttr[attrCount++] = new AttrType(AttrType.attrInteger);
		} else if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrString) {
			combinedAttr[attrCount++] = new AttrType(AttrType.attrString);
			combinedStrSizes[strCount++] = 20;
		}
		combinedProjection = new FldSpec[combinedAttrCount];
		for (int attr = 0; attr < combinedAttrCount; attr++) {
			combinedProjection[attr] = new FldSpec(new RelSpec(RelSpec.outer),
					attr + 1);
		}

		try {
			combinedTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
			mainTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
			randomTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
		} catch (InvalidTypeException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvalidTupleSizeException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	public Tuple get_next() throws IOException, JoinsException, IndexException,
			InvalidTupleSizeException, InvalidTypeException,
			PageNotReadException, TupleUtilsException, PredEvalException,
			SortException, LowMemException, UnknowAttrType,
			UnknownKeyTypeException, Exception {
		if (firstTime) {
			createTopKTuples();
		}

		return new Tuple();

	}

	/*private boolean validTuple(Tuple tempTuple, int relationNumber) {
		boolean returnValue = true;
		try {
			for (int i = 0; i < outFilter.length; i++) {
				AttrType left = outFilter[i].type2;
				FldSpec operand1Sym = outFilter[i].operand1.symbol;
				int colNo = operand1Sym.offset;
				int relNo = operand1Sym.relation.key;
				if (relNo == relationNumber) {
					switch (left.attrType) {
					case AttrType.attrInteger:
						int rightPart = outFilter[i].operand2.integer;
						int leftInt = tempTuple.getIntFld(colNo);
						switch (outFilter[i].op.attrOperator) {
						case AttrOperator.aopEQ:
							if (rightPart == leftInt)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGE:
							if (leftInt >= rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGT:
							if (leftInt > rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLE:
							if (leftInt <= rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLT:
							if (leftInt < rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopNE:
							if (leftInt != rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						}
						break;
					case AttrType.attrReal:
						float rightFloat = outFilter[i].operand2.real;
						float leftFloat = tempTuple.getFloFld(colNo);
						switch (outFilter[i].op.attrOperator) {
						case AttrOperator.aopEQ:
							if (leftFloat == rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGE:
							if (leftFloat >= rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGT:
							if (leftFloat > rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLE:
							if (leftFloat <= rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLT:
							if (leftFloat < rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopNE:
							if (leftFloat != rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						}
						break;
					case AttrType.attrString:
						String rightString = outFilter[i].operand2.string;
						String leftString = tempTuple.getStrFld(colNo);
						switch (outFilter[i].op.attrOperator) {
						case AttrOperator.aopEQ:
							if (leftString.equalsIgnoreCase(rightString))
								return returnValue;
							else
								return !returnValue;
						case AttrOperator.aopGE:
							if (leftString.compareToIgnoreCase(rightString) >= 0)
								return returnValue;
							else
								return !returnValue;
						case AttrOperator.aopGT:
							if (leftString.compareToIgnoreCase(rightString) > 0)
								return returnValue;
							else
								return !returnValue;
						case AttrOperator.aopLE:
							if (leftString.compareToIgnoreCase(rightString) <= 0)
								return returnValue;
							else
								return !returnValue;
						case AttrOperator.aopLT:
							if (leftString.compareToIgnoreCase(rightString) < 0)
								return returnValue;
							else
								return !returnValue;
						case AttrOperator.aopNE:
							if (!(leftString.equalsIgnoreCase(rightString)))
								return returnValue;
							else
								return !returnValue;
						}
						break;
					}
				}
			}
		} catch (Exception e) {
			// System.out.println("Exception while processing Tuple in Top Rank Join");
		}
		return returnValue;
	}*/

	public void createTopKTuples() {
		int count = 0;
		Tuple fileTuple = new Tuple();
		RID ridScan = new RID();
		int keySize = 4;

		AttrType keyAttrType = new AttrType(
				inputRelations[0][joinColumns[0]].attrType);
		try {
			tempFile.deleteFile();
			tempFile = new Heapfile("TempResults.in");
			if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrString)
				keySize = 20;
			tempFileBtf = new BTreeFile("BTreeIndex",
					inputRelations[0][joinColumns[0]].attrType, keySize, 1);

		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		while (count < knumberOfTuples) {
			for (int relNum = 0; relNum < numberOfTables; relNum++) {
				try {
					fileTuple = iterators[relNum].get_next();
					if (fileTuple == null)
						continue;
					String strKey = "";
					ridScan = ConstantVars.getGlobalRID();
					/*String rid = Integer.toString(ridScan.pageNo.pid) + "_"
							+ Integer.toString(ridScan.slotNo);*/
					try {
						switch (inputRelations[relNum][joinColumns[relNum]].attrType) {
						case AttrType.attrInteger:
							strKey = String.valueOf(fileTuple
									.getIntFld(joinColumns[relNum] + 1));
							break;
						case AttrType.attrString:
							strKey = fileTuple
									.getStrFld(joinColumns[relNum] + 1);
							break;
						}
					} catch (Exception e) {
						e.printStackTrace();
						Runtime.getRuntime().exit(1);
					}
					count += sequentialAccess(fileTuple, keyAttrType, strKey,
							relNum, false);
					topkMinSum[relNum] = fileTuple.getScore();
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		randomAcess();
		writeTopK();
		get_topK();
		try {
			fScan = new FileScan("TempResults.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple testTuple = new Tuple();
		try {
			while ((testTuple = fScan.get_next()) != null) {
				testTuple.print(combinedAttr);
			}
			fScan.close();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private void randomAcess() {
		FileScan rScan = null;
		try {
			rScan = new FileScan("TempResults.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		AttrType keyAttrType = inputRelations[0][joinColumns[0]];
		try {
			while ((mainTuple = rScan.get_next()) != null) {
				RID ridScan = ConstantVars.getGlobalRID();
				RID mainRID = new RID();
				mainRID.pageNo = ridScan.pageNo;
				mainRID.slotNo = ridScan.slotNo;
				if (mainRID.equals(lastAccessedRID)) {
					break;
				}
				String strKey = "";
				if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrInteger) {
					strKey = String.valueOf(mainTuple
							.getIntFld(combinedAttrCount));
				} else {
					strKey = mainTuple.getStrFld(combinedAttrCount);
				}
				/*String rid = Integer.toString(ridScan.pageNo.pid) + "-"
						+ Integer.toString(ridScan.slotNo);*/
				if (mainTuple.getIntFld(combinedAttrCount - 1) != numberOfTables) {
					randomTuple.tupleCopy(mainTuple);
					tempFile.deleteRecord(ridScan);
					checkForThreshold(strKey, keyAttrType, mainRID, true, false);
				} else {
					relMap = new HashMap<Integer, Boolean>();
					relMap.put(0, true);
					randomTuple.tupleCopy(mainTuple);
					randomTuple.setIntFld(combinedAttrCount - 1, 1);
					checkForThreshold(strKey, keyAttrType, mainRID, true, true);
					relMap = new HashMap<Integer, Boolean>();
					relMap.put(1, true);
					randomTuple.tupleCopy(mainTuple);
					randomTuple.setIntFld(combinedAttrCount - 1, 1);
					checkForThreshold(strKey, keyAttrType, mainRID, true, true);
				}
				mainTuple = null;
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	private boolean checkForThreshold(String strKey, AttrType keyAttrType,
			RID mainRID, boolean first, boolean afterRandom) {
		BTreeFile btf1 = null;
		if (!checkFirst)
			checkFirst = true;
		for (int i = 0; i < numberOfTables; i++) {
			if (!afterRandom && relationExists(i, strKey, randomTuple)) {
				continue;
			} else {
				if (afterRandom && relMap.containsKey(i))
					continue;
				if (afterRandom)
					relMap.put(i, true);
				try {
					CondExpr[] randomExpr = new CondExpr[2];
					randomExpr[0] = new CondExpr();
					randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
					randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
					randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(
							RelSpec.outer), joinColumns[i] + 1);
					if (keyAttrType.attrType == AttrType.attrInteger) {
						randomExpr[0].type2 = new AttrType(AttrType.attrInteger);
						randomExpr[0].operand2.integer = randomTuple
								.getIntFld(combinedAttrCount);
					} else if (keyAttrType.attrType == AttrType.attrString) {
						randomExpr[0].type2 = new AttrType(AttrType.attrString);
						randomExpr[0].operand2.string = randomTuple
								.getStrFld(combinedAttrCount);
					}
					randomExpr[0].next = null;
					randomExpr[1] = null;
					FldSpec[] fSpec = new FldSpec[inputRelations[i].length];
					for (int j = 0; j < inputRelations[i].length; j++) {
						fSpec[j] = new FldSpec(new RelSpec(RelSpec.outer),
								j + 1);
					}
					IndexScan iScan = new IndexScan(new IndexType(
							IndexType.B_Index), fileNames[i],
							indexFileNames[i], inputRelations[i],
							stringSizes[i], inputRelations[i].length,
							inputRelations[i].length, fSpec, randomExpr,
							joinColumns[i] + 1, false);
					Tuple indexTuple = new Tuple();
					Heapfile interFile = new Heapfile("interFile" + i + ".in");
					RID prevRID = new RID();
					HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
					while ((indexTuple = iScan.get_next()) != null) {
						RID currRID = iScan.getRID();
						String scanKey = "" + currRID.pageNo.pid + "_"+ currRID.slotNo;
						if (randomMap.containsKey(scanKey)) {
							continue;
						} else {
							randomMap.put(scanKey, true);
						}
						if (currRID.pageNo.pid == prevRID.pageNo.pid && currRID.slotNo == prevRID.slotNo)
							continue;
						prevRID.pageNo.pid = currRID.pageNo.pid;
						prevRID.slotNo = currRID.slotNo;
						interFile.insertRecord(indexTuple.getTupleByteArray());
					}
					if (interFile.getRecCnt() > 0) {
						FileScan fm1 = null;
						try {
							fm1 = new FileScan("interFile" + i + ".in",
									inputRelations[i], stringSizes[i],
									(short) inputRelations[i].length,
									inputRelations[i].length, fSpec, null);
						} catch (Exception e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						TupleOrder order = new TupleOrder(TupleOrder.Descending);
						Iterator topIterator = new Sort(inputRelations[i],
								(short) inputRelations[i].length,
								stringSizes[i], fm1,
								inputRelations[i].length - 1, order, 4, 10);
						Tuple newTuple;
						while ((newTuple = topIterator.get_next()) != null) {
						
							updateTuple(newTuple, randomTuple, i,
									getTupleOffset(i));
							randomTuple.setIntFld(combinedAttrCount - 1,randomTuple.getIntFld(combinedAttrCount - 1) + 1);
							if (randomTuple.getIntFld(combinedAttrCount - 1) == numberOfTables) {
								float score = 0.0f;
								for (int relNum = 0; relNum < numberOfTables; relNum++) {
									score += randomTuple.getFloFld(getTupleOffset(relNum)+ inputRelations[relNum].length- 2);
								}
								score = score / numberOfTables;
								if (afterRandom) {
									randomTuple.setFloFld(combinedAttrCount - 2, score);
									boolean checkFlag = checkTupleExists(randomTuple, strKey, keyAttrType,"TempResults.in", "BTreeIndex");
									if (score >= topKmin && !checkFlag) {
										RID rid = tempFile.insertRecord(randomTuple.getTupleByteArray());
										insertIntoBTree(strKey, rid,keyAttrType);
										randomTuple.setIntFld(combinedAttrCount - 1,randomTuple.getIntFld(combinedAttrCount - 1) - 1);
									} else {
										randomTuple.setIntFld(combinedAttrCount - 1,randomTuple.getIntFld(combinedAttrCount - 1) - 1);
									}
								} else {
									randomTuple.setFloFld(combinedAttrCount - 2, score);
									RID rid = tempFile.insertRecord(randomTuple.getTupleByteArray());
									insertIntoBTree(strKey, rid, keyAttrType);
									randomTuple.setIntFld(combinedAttrCount - 1,randomTuple.getIntFld(combinedAttrCount - 1) - 1);
								}
							} else {
								if (!afterRandom) {
									checkForThreshold(strKey,keyAttrType, mainRID, false, false);
								} else {
									checkForThreshold(strKey,keyAttrType, mainRID, false, true);
								}
								randomTuple.setIntFld(combinedAttrCount - 1,randomTuple.getIntFld(combinedAttrCount - 1) - 1);
							}
						}
						topIterator.close();
						fm1.close();
						interFile.deleteFile();
						return false;
					}
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
		// TODO Auto-generated method stub
		return false;
	}

	private boolean checkTupleExists(Tuple fileTuple, String strKey,
			AttrType keyAttrType, String fileName, String indexName) {
		// TODO Auto-generated method stub
		CondExpr[] randomExpr = new CondExpr[2];
		randomExpr[0] = new CondExpr();
		randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
		randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
		randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer),
				combinedAttrCount);
		if (keyAttrType.attrType == AttrType.attrInteger) {
			randomExpr[0].type2 = new AttrType(AttrType.attrInteger);
			randomExpr[0].operand2.integer = Integer.parseInt(strKey);
		} else if (keyAttrType.attrType == AttrType.attrString) {
			randomExpr[0].type2 = new AttrType(AttrType.attrString);
			randomExpr[0].operand2.string = strKey;
		}
		randomExpr[0].next = null;
		randomExpr[1] = null;
		IndexScan tempScan = null;
		RID prevRID = new RID();
		HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
		try {
			tempScan = new IndexScan(new IndexType(IndexType.B_Index),
					fileName, indexName, combinedAttr, combinedStrSizes,
					combinedAttrCount, combinedAttrCount, combinedProjection,
					randomExpr, combinedAttrCount, false);
			Tuple t = null;
			while ((t = tempScan.get_next()) != null) {
				RID currRID = tempScan.getRID();
				String scanKey = "" + currRID.pageNo.pid + "_" + currRID.slotNo;
				if (randomMap.containsKey(scanKey)) {
					continue;
				} else {
					randomMap.put(scanKey, true);
				}
				if (currRID.pageNo.pid == prevRID.pageNo.pid
						&& currRID.slotNo == prevRID.slotNo)
					continue;
				prevRID.pageNo.pid = currRID.pageNo.pid;
				prevRID.slotNo = currRID.slotNo;
				int count = 0;
				for (int relNum = 0; relNum < numberOfTables; relNum++) {
					int offset = getTupleOffset(relNum)
							+ inputRelations[relNum].length - 1;
					if ((t.getStrFld(offset)
							.equals(fileTuple.getStrFld(offset)))) {
						count++;
					}
				}
				if (count == numberOfTables) {
					return true;
				}
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return false;
	}

	private int sequentialAccess(Tuple fileTuple, AttrType keyAttrType,
			String strKey, int relNum, boolean updateFlag) {
		combinedTuple = new Tuple();
		RID insertRid = new RID();
		try {
			combinedTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		int count = 0;
		CondExpr[] randomExpr = new CondExpr[2];
		randomExpr[0] = new CondExpr();
		randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
		randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
		randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer),
				combinedAttrCount);
		if (keyAttrType.attrType == AttrType.attrInteger) {
			randomExpr[0].type2 = new AttrType(AttrType.attrInteger);
			randomExpr[0].operand2.integer = Integer.parseInt(strKey);
		} else if (keyAttrType.attrType == AttrType.attrString) {
			randomExpr[0].type2 = new AttrType(AttrType.attrString);
			randomExpr[0].operand2.string = strKey;
		}
		randomExpr[0].next = null;
		randomExpr[1] = null;
		IndexScan tempScan = null;
		RID prevRID = new RID();
		try {
			tempScan = new IndexScan(new IndexType(IndexType.B_Index),
					"TempResults.in", "BTreeIndex", combinedAttr,
					combinedStrSizes, combinedAttrCount, combinedAttrCount,
					combinedProjection, randomExpr, combinedAttrCount, false);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		boolean keyExists = false;
		try {
			HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
			HashMap<String, Boolean> ridMap = new HashMap<String, Boolean>();
			while ((t = tempScan.get_next()) != null) {
				RID currRID = tempScan.getRID();
				String scanKey = "" + currRID.pageNo.pid + "_" + currRID.slotNo;
				if (randomMap.containsKey(scanKey)) {
					continue;
				} else {
					randomMap.put(scanKey, true);
				}
				if (currRID.pageNo.pid == prevRID.pageNo.pid
						&& currRID.slotNo == prevRID.slotNo)
					continue;
				prevRID.pageNo.pid = currRID.pageNo.pid;
				prevRID.slotNo = currRID.slotNo;
				keyExists = true;
				combinedTuple.tupleCopy(t);
				if (relationExists(relNum, strKey, combinedTuple)) {
					String relRid = getRid(relNum, combinedTuple);
					if (ridMap.containsKey(relRid)) {
						continue;
					} else {
						ridMap.put(relRid, true);
					}
					updateTuple(fileTuple, combinedTuple, relNum,
							getTupleOffset(relNum));
					insertRid = tempFile.insertRecord(combinedTuple
							.getTupleByteArray());
					insertIntoBTree(strKey, insertRid, keyAttrType);
				} else {
					insertRid = ConstantVars.getGlobalRID();
					updateTuple(fileTuple, combinedTuple, relNum,
							getTupleOffset(relNum));
					combinedTuple.setIntFld(combinedAttrCount - 1,
							combinedTuple.getIntFld(combinedAttrCount - 1) + 1);
					tempFile.updateRecord(insertRid, combinedTuple);
				}
				if (combinedTuple.getIntFld(combinedAttrCount - 1) == numberOfTables) {
					float score = 0.0f;
					for (int i = 0; i < numberOfTables; i++) {
						score += combinedTuple.getFloFld(getTupleOffset(i)
								+ inputRelations[i].length - 2);
					}
					score = score / numberOfTables;
					combinedTuple.setFloFld(combinedAttrCount - 2, score);
					if (!updateFlag) {
						tempFile.updateRecord(insertRid, combinedTuple);
						count++;
						if (topKmin > score)
							topKmin = score;
						lastAccessedRID = insertRid;
					} else {
						if (score > topKmin) {
							outFile.insertRecord(combinedTuple
									.getTupleByteArray());
						}
					}
				}
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (!keyExists) {
			updateTuple(fileTuple, combinedTuple, relNum,
					getTupleOffset(relNum));
			try {
				combinedTuple.setIntFld(combinedAttrCount - 1,
						combinedTuple.getIntFld(combinedAttrCount - 1) + 1);
				if (keyAttrType.attrType == AttrType.attrInteger) {
					combinedTuple.setIntFld(combinedAttrCount,
							Integer.parseInt(strKey));
				} else if (keyAttrType.attrType == AttrType.attrString) {
					combinedTuple.setStrFld(combinedAttrCount, strKey);
				}
				if (!updateFlag) {
					insertRid = tempFile.insertRecord(combinedTuple
							.getTupleByteArray());
					insertIntoBTree(strKey, insertRid, keyAttrType);
				}
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		// TODO Auto-generated method stub
		return count;
	}

	private String getRid(int relNum, Tuple fileTuple) {
		StringBuffer rid = new StringBuffer();
		for (int i = 0; i < inputRelations.length; i++) {
			if (i == relNum)
				continue;
			int ridOffset = getTupleOffset(i) + inputRelations[i].length - 1;
			try {
				if (!fileTuple.getStrFld(ridOffset).equals("")) {
					rid.append(fileTuple.getStrFld(ridOffset));
					rid.append("_");
				}
			} catch (FieldNumberOutOfBoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		// TODO Auto-generated method stub
		return rid.toString();
	}

	public boolean relationExists(int relNum, String strKey, Tuple jTuple) {
		int keyOffset = getTupleOffset(relNum);
		if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrInteger) {
			try {
				if (jTuple.getIntFld(keyOffset) == Integer.parseInt(strKey))
					return true;
			} catch (FieldNumberOutOfBoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} else if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrString) {
			try {
				if ((jTuple.getStrFld(keyOffset).equals(strKey)))
					return true;
			} catch (FieldNumberOutOfBoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return false;
	}

	public void insertIntoBTree(String strKey, RID rid, AttrType keyAttrType) {
		try {
			switch (keyAttrType.attrType) {
			case AttrType.attrInteger:
				tempFileBtf.insert(new IntegerKey(Integer.parseInt(strKey)),
						rid);
				break;
			case AttrType.attrString:
				tempFileBtf.insert(new StringKey(strKey), rid);
				break;
			}
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	public void close() throws JoinsException, IOException, IndexException {
		if (!closeFlag) {

			try {
				for (int i = 0; i < numberOfTables; i++)
					iterators[i].close();
			} catch (Exception e) {
				throw new JoinsException(e,
						"NestedLoopsJoin.java: error in closing iterator.");
			}
			closeFlag = true;
		}
	}

	public int num_scanned(int in_rel) {
		if (in_rel < numberOfTables && in_rel >= 0)
			return numOfScanned[in_rel];
		else
			return -1;
	}

	public int num_probed(int in_rel) {
		if (in_rel < numberOfTables && in_rel >= 0)
			return numOfProbed[in_rel];
		else
			return -1;
	}

	public void get_topK() {
		FldSpec[] tProjection = new FldSpec[proj_list.length + 1];
		AttrType[] attrType = new AttrType[proj_list.length + 1];
		ArrayList<Short> stringSizes = new ArrayList<Short>();
		for (int i = 0; i < tProjection.length - 1; i++) {
			tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer),
					getTupleOffset(proj_list[i].relation.key)
							+ proj_list[i].offset - 1);
			/*int p = getTupleOffset(proj_list[i].relation.key)
					+ proj_list[i].offset - 1;*/
			attrType[i] = inputRelations[proj_list[i].relation.key][proj_list[i].offset - 1];
			if (attrType[i].attrType == AttrType.attrString) {
				stringSizes.add((short) 20);
			}
		}
		attrType[proj_list.length] = new AttrType(AttrType.attrReal);
		tProjection[proj_list.length] = new FldSpec(new RelSpec(RelSpec.outer),
				combinedAttrCount - 2);
		short[] strSizes = new short[stringSizes.size()];
		for (int i = 0; i < stringSizes.size(); i++) {
			strSizes[i] = stringSizes.get(i);
		}
		FileScan fm1 = null;
		try {
			fm1 = new FileScan("TopRankJoin.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					attrType.length, tProjection, null);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple tuple1 = null;
		int topK = knumberOfTuples;
		while (topK > 0) {
			try {
				if ((tuple1 = fm1.get_next()) != null) {
					tuple1.print(attrType);
				}
				topK--;
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		try {
			topKmin = tuple1.getFloFld(attrType.length);
		} catch (FieldNumberOutOfBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private void writeTopK() {
		FileScan fm1 = null;

		try {
			outFile.deleteFile();
			outFile = new Heapfile("TopRankJoin.in");
			fm1 = new FileScan("TempResults.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		TupleOrder order = new TupleOrder(TupleOrder.Descending);
		Iterator topIterator = null;
		try {
			topIterator = new Sort(combinedAttr, (short) combinedAttrCount,
					combinedStrSizes, fm1, combinedAttrCount - 2, order, 4,
					n_buf_pgs);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple tuple1;
		int topK = knumberOfTuples;
		while (topK > 0) {
			try {
				if ((tuple1 = topIterator.get_next()) != null) {
					outFile.insertRecord(tuple1.getTupleByteArray());
					String key = null;
					if (inputRelations[0][0].attrType == AttrType.attrInteger) {
						key = String.valueOf(tuple1
								.getIntFld(combinedAttrCount));
					} else if (inputRelations[0][0].attrType == AttrType.attrString) {
						key = tuple1.getStrFld(combinedAttrCount);
					}
					for (int relNum = 0; relNum < numberOfTables; relNum++) {
						int offset = getTupleOffset(relNum)
								+ inputRelations[relNum].length - 2;
						ArrayList<Float> scoreArray = new ArrayList<Float>();
						Float score = 1.0f;
						if (keyMap.containsKey(key)) {
							scoreArray = keyMap.get(key);
							if (relNum < scoreArray.size())
								score = scoreArray.get(relNum);
						}
						if (score > tuple1.getFloFld(offset)) {
							if (keyMap.containsKey(key)
									&& relNum < scoreArray.size())
								scoreArray
										.set(relNum, tuple1.getFloFld(offset));
							else
								scoreArray.add(tuple1.getFloFld(offset));
							keyMap.put(key, scoreArray);
						}
					}
				}
				topK--;
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

	}

	private int getTupleOffset(int tableIndex) {
		int offset = 0;
		if (tableIndex == 0) {
			return 1;
		}
		for (int i = 0; i < tableIndex; i++) {
			offset += inputRelations[i].length;
		}
		return offset + 1;

	}

	private void updateTuple(Tuple inTuple, Tuple outTuple, int tableIndex,
			int offset) {
		int fieldCount = 1;
		int attrLength = inputRelations[tableIndex].length;
		for (int tField = 1; tField <= attrLength; tField++) {
			try {
				switch (inputRelations[tableIndex][tField - 1].attrType) {
				case AttrType.attrInteger:
					outTuple.setIntFld(offset, inTuple.getIntFld(fieldCount));
					fieldCount++;
					offset++;
					break;
				case AttrType.attrReal:
					outTuple.setFloFld(offset, inTuple.getFloFld(fieldCount));
					fieldCount++;
					offset++;
					break;
				case AttrType.attrString:
					outTuple.setStrFld(offset, inTuple.getStrFld(fieldCount));
					fieldCount++;
					offset++;
					break;
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	public void updateFA(String[] updateIndexNameList, String[] updateFiles,
			IndexType[] update_index, Iterator[] updateIteratorList) {
		int count = 0;
		updateFileNames = updateFiles;
		updateIndexNames = updateIndexNameList;
		String strKey = null;
		AttrType keyAttrType = inputRelations[0][joinColumns[0]];
		Scan scan = null;
		RID sScanRid = new RID();
		String sTupleKey = "";
		int tupleKey = 0;
		Tuple temp1 = null;
		int keySize = 4;
		Tuple scanTuple = new Tuple();
		if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrString) {
			keySize = 20;
		}
		try {
			scanTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
			insertIndex = new BTreeFile("BTreeIndexInsert",
					inputRelations[0][joinColumns[0]].attrType, keySize, 1);
			scan = new Scan(outFile);
			temp1 = scan.getNext(sScanRid);
		} catch (Exception e) {
			e.printStackTrace();
		}
		while (temp1 != null) {
			scanTuple.tupleCopy(temp1);
			try {
				switch (inputRelations[0][joinColumns[0]].attrType) {
				case AttrType.attrInteger:
					tupleKey = scanTuple.getIntFld(combinedAttrCount);
					insertIndex.insert(new IntegerKey(tupleKey), sScanRid);
					break;
				case AttrType.attrString:
					sTupleKey = scanTuple.getStrFld(combinedAttrCount);
					insertIndex.insert(new StringKey(sTupleKey), sScanRid);
					break;
				}
				temp1 = scan.getNext(sScanRid);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		for (int i = 0; i < numberOfTables; i++) {
			if (!updateFileNames[i].equals(""))
				count++;
		}
		int relCount = 0;
		while (relCount < count) {
			for (int relNum = 0; relNum < numberOfTables; relNum++) {
				if (updateIteratorList[relNum] != null) {
					try {
						Tuple fileTuple = updateIteratorList[relNum].get_next();
						if (fileTuple == null) {
							relCount++;
							if (count == relCount) {
								break;
							}
							continue;
						}
						if (inputRelations[relNum][joinColumns[relNum]].attrType == AttrType.attrInteger) {
							strKey = String.valueOf(fileTuple
									.getIntFld(joinColumns[relNum] + 1));
						} else if (inputRelations[relNum][joinColumns[relNum]].attrType == AttrType.attrString) {
							strKey = fileTuple
									.getStrFld(joinColumns[relNum] + 1);
						}
						if (keyMap.containsKey(strKey)) {
							ArrayList<Float> scoreArray = keyMap.get(strKey);
							if (fileTuple
									.getFloFld(inputRelations[relNum].length - 1) < scoreArray
									.get(relNum)) {
								continue;
							}
							updateTopRank(fileTuple, keyAttrType, strKey,
									relNum);
						} else {
							sequentialAccess(fileTuple, keyAttrType, strKey,
									relNum, true);
						}

					} catch (Exception e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
			}
		}
		updateTopK();
	}

	public void updateTopRank(Tuple fileTuple, AttrType keyAttrType,
			String strKey, int relNum) {
		CondExpr[] randomExpr = new CondExpr[2];
		randomExpr[0] = new CondExpr();
		randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
		randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
		randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer),
				combinedAttrCount);
		if (keyAttrType.attrType == AttrType.attrInteger) {
			randomExpr[0].type2 = new AttrType(AttrType.attrInteger);
			randomExpr[0].operand2.integer = Integer.parseInt(strKey);
		} else if (keyAttrType.attrType == AttrType.attrString) {
			randomExpr[0].type2 = new AttrType(AttrType.attrString);
			randomExpr[0].operand2.string = strKey;
		}
		randomExpr[0].next = null;
		randomExpr[1] = null;
		try {
			IndexScan iScan = new IndexScan(new IndexType(IndexType.B_Index),
					"TopRankJoin.in", "BTreeIndexInsert", combinedAttr,
					combinedStrSizes, combinedAttrCount, combinedAttrCount,
					combinedProjection, randomExpr, combinedAttrCount, false);
			Tuple indexTuple = new Tuple();
			indexTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
			RID prevRID = new RID();
			HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
			while ((indexTuple = iScan.get_next()) != null) {
				indexTuple.print(combinedAttr);
				RID currRID = iScan.getRID();
				String scanKey = "" + currRID.pageNo.pid + "_" + currRID.slotNo;
				if (randomMap.containsKey(scanKey)) {
					continue;
				} else {
					randomMap.put(scanKey, true);
				}
				if (currRID.pageNo.pid == prevRID.pageNo.pid && currRID.slotNo == prevRID.slotNo)
					continue;
				prevRID.pageNo.pid = currRID.pageNo.pid;
				prevRID.slotNo = currRID.slotNo;
				updateTuple(fileTuple, indexTuple, relNum,
						getTupleOffset(relNum));
				float score = 0.0f;
				for (int i = 0; i < numberOfTables; i++) {
					score += indexTuple.getFloFld(getTupleOffset(i)+ inputRelations[i].length - 2);
				}
				score = score / numberOfTables;
				indexTuple.setFloFld(combinedAttrCount - 2, score);
				if (score > topKmin && !(checkTupleExists(indexTuple, strKey, keyAttrType,"TopRankJoin.in", "BTreeIndexInsert"))) {
					RID rid = outFile.insertRecord(indexTuple.getTupleByteArray());
					switch (keyAttrType.attrType) {
					case AttrType.attrInteger:
						insertIndex.insert(
								new IntegerKey(Integer.parseInt(strKey)), rid);
						break;
					case AttrType.attrString:
						insertIndex.insert(new StringKey(strKey), rid);
						break;
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void deleteFA(String[] deleteIndexNameList, String[] deleteFiles,
			AttrType[][] updateAttrTypeList, short[][] updateStrSizesList,
			IndexType[] delete_index, Iterator[] deleteIteratorList) {
		// TODO Auto-generated method stub

	}

	public void updateTopK() {
		FileScan fm1 = null;
		Heapfile finalFile = null;
		try {
			finalFile = new Heapfile("UpdateTop.in");
			fm1 = new FileScan("TopRankJoin.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		TupleOrder order = new TupleOrder(TupleOrder.Descending);
		Iterator topIterator = null;
		try {
			topIterator = new Sort(combinedAttr, (short) combinedAttrCount,
					combinedStrSizes, fm1, combinedAttrCount - 2, order, 4,
					n_buf_pgs);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple tuple1;
		int topK = knumberOfTuples;
		while (topK > 0) {
			try {
				if ((tuple1 = topIterator.get_next()) != null) {
					tuple1.print(combinedAttr);
					finalFile.insertRecord(tuple1.getTupleByteArray());
				}
				topK--;
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		FldSpec[] tProjection = new FldSpec[proj_list.length + 1];
		AttrType[] attrType = new AttrType[proj_list.length + 1];
		ArrayList<Short> stringSizes = new ArrayList<Short>();
		for (int i = 0; i < tProjection.length - 1; i++) {
			tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer),
					getTupleOffset(proj_list[i].relation.key)
							+ proj_list[i].offset - 1);
			attrType[i] = inputRelations[proj_list[i].relation.key][proj_list[i].offset - 1];
			if (attrType[i].attrType == AttrType.attrString) {
				stringSizes.add((short) 20);
			}
		}
		attrType[proj_list.length] = new AttrType(AttrType.attrReal);
		tProjection[proj_list.length] = new FldSpec(new RelSpec(RelSpec.outer),
				combinedAttrCount - 2);
		short[] strSizes = new short[stringSizes.size()];
		for (int i = 0; i < stringSizes.size(); i++) {
			strSizes[i] = stringSizes.get(i);
		}
		FileScan fm2 = null;
		try {
			fm2 = new FileScan("UpdateTop.in", combinedAttr, combinedStrSizes,
					(short) combinedAttrCount, attrType.length, tProjection,
					null);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple finalTuple = null;
		topK = knumberOfTuples;

		while (topK > 0) {
			try {
				if ((finalTuple = fm2.get_next()) != null) {
					finalTuple.print(attrType);
				}
				topK--;
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

	}
}