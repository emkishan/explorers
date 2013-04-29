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

public class TopFASC extends Iterator {

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
	private int numOfScanned, numOfProbed;
	private Heapfile heapFiles[], outFile;
	private boolean firstTime;
	private String[] indexFileNames;
	private boolean duplFlag = false;
	private String[] fileNames;
	private String[] updateFileNames;
	private String[] updateIndexNames;
	private String[] interIndexName, interFileName;
	private Tuple combinedTuple = new Tuple();
	private Tuple randomTuple = new Tuple();
	private Tuple t = new Tuple();
	private IndexType[] interIndexType;
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
	private BTreeFile[] interBTF;
	private BTreeFile tempFileBtf = null;
	private BTreeFile insertIndex = null;
	float[] indicators;
	int arr[];

	public TopFASC(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			IndexType[] index, java.lang.String[] indNames, int amt_of_mem,
			CondExpr[] outFilter, FldSpec[] proj_list, int n_out_flds, int num,
			int rank, String[] fileNames) throws IOException,
			TopRankJoinException {
		numberOfTables = numTables;
		inputRelations = new AttrType[numTables][];
		indexFileNames = indNames;
		joinColumns = join_col_in;
		outFile = null;
		iterators = am;
		this.fileNames = fileNames;
		topkMinSum = new float[numberOfTables];
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
		this.outFilter = new CondExpr[outFilter.length];
		this.proj_list = new FldSpec[proj_list.length];
		for (int i = 0; i < outFilter.length; i++) {
			this.outFilter[i] = outFilter[i];
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

	public void createTopKTuples() {
		int count = 0;
		Tuple fileTuple = new Tuple();
		RID ridScan = new RID();
		int keySize = 4;
		numOfScanned = 0;
		numOfProbed = 0;
		int some = 0;
    	int topKCounter=0;
		int relNum = 0;
    	int nextRel=-1;
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
		topkMinSum = new float[knumberOfTuples];
		for(int i=0;i<knumberOfTuples;i++){
			topkMinSum[i] = 1.0f;
		}
		while (count < knumberOfTuples) {
			for (int i = 0; i < numberOfTables; i++) {
				try {
					if(some>2*knumberOfTuples){
						//nextRel=calculateIndicator();
						nextRel=checkIndicator();
						relNum=nextRel;
					}
					else{
						relNum=i;
					}
					fileTuple = iterators[relNum].get_next();
					if (fileTuple == null)
						continue;
					numOfScanned++;
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
				//testTuple.print(combinedAttr);
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
							numOfProbed++;
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
					updateTuple(fileTuple, combinedTuple, relNum,getTupleOffset(relNum));
					insertRid = tempFile.insertRecord(combinedTuple.getTupleByteArray());
					insertIntoBTree(strKey, insertRid, keyAttrType);
				} else {
					insertRid = ConstantVars.getGlobalRID();
					updateTuple(fileTuple, combinedTuple, relNum,getTupleOffset(relNum));
					combinedTuple.setIntFld(combinedAttrCount - 1,combinedTuple.getIntFld(combinedAttrCount - 1) + 1);
					tempFile.updateRecord(insertRid, combinedTuple);
				}
				if (combinedTuple.getIntFld(combinedAttrCount - 1) == numberOfTables) {
					float score = 0.0f;
					for (int i = 0; i < numberOfTables; i++) {
						score += combinedTuple.getFloFld(getTupleOffset(i)+ inputRelations[i].length - 2);
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
							outFile.insertRecord(combinedTuple.getTupleByteArray());
						}
						else{
							combinedTuple = new Tuple();
							combinedTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
							updateTuple(fileTuple, combinedTuple, relNum, getTupleOffset(relNum));
							tempFile.insertRecord(combinedTuple.getTupleByteArray());
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

	public int num_scanned() {
		return numOfScanned;
	}

	public int num_probed() {
		return numOfProbed;
	}

	public void get_topK() {
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
		fm1.close();
	}

	private void writeTopK() {
		FileScan fm1 = null;

		try {
			if(outFile.getRecCnt()>0)
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
						int offset = getTupleOffset(relNum)+ inputRelations[relNum].length - 2;
						float minScore = tuple1.getFloFld(offset);
						ArrayList<Float> scoreArray = new ArrayList<Float>();
						Float score = 1.0f;
						if(topkMinSum[relNum]>minScore){
							topkMinSum[relNum] = minScore;
						}
						if (keyMap.containsKey(key)) {
							scoreArray = keyMap.get(key);
							if (relNum < scoreArray.size())
								score = scoreArray.get(relNum);
						}
						if (score > tuple1.getFloFld(offset)) {
							if (keyMap.containsKey(key)&& relNum < scoreArray.size())
								scoreArray.set(relNum, minScore);
							else
								scoreArray.add(minScore);
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
		for (int i = 0; i < numberOfTables; i++) {
			if (!updateFileNames[i].equals(""))
				count++;
		}
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
							float tupleScore = fileTuple.getFloFld(inputRelations[relNum].length - 1);
							if (tupleScore < scoreArray.get(relNum)&& tupleScore<topkMinSum[relNum]) {
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

	public void deleteFA(Iterator[] del) {
		// TODO Auto-generated method stub
		initializeBTreeFileInter();
		for(int relation=0;relation<numberOfTables;relation++){
			if(del[relation]!=null){
				deleteTuple(del[relation],relation);
			}
		}
	}

	
	public void deleteTuple(Iterator iter,int relation){
		Tuple tuple = new Tuple();
		AttrType attrType = inputRelations[relation][joinColumns[relation]];
		try{
			while((tuple=iter.get_next())!=null){
				//Get the tuple's key
				String key="";
				if(attrType.attrType==AttrType.attrInteger){
					key = String.valueOf(tuple.getIntFld(joinColumns[relation]+1));
				}
				else{
					key = tuple.getStrFld(joinColumns[relation]+1);
				}
				//Condition for scanning the original relation
				int attrCount = inputRelations[relation].length;
				FldSpec[] tProjection = new FldSpec[attrCount];
				for (int i = 0; i < attrCount; i++)
					tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);

				CondExpr[] expr = new CondExpr[2];
				expr[0] = new CondExpr();
				expr[0].op = new AttrOperator(AttrOperator.aopEQ);
				expr[0].type1 = new AttrType(AttrType.attrSymbol);
				expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[relation]+1);
				if(attrType.attrType==AttrType.attrInteger){
					expr[0].type2 = new AttrType(AttrType.attrInteger);
					expr[0].operand2.integer = Integer.parseInt(key);
				}
				else{
					expr[0].type2 = new AttrType(AttrType.attrString);
					expr[0].operand2.string= key;
				}			
				expr[0].next = null;
				expr[1] = null;
				
				IndexScan tempIndex = new IndexScan(new IndexType(IndexType.B_Index), fileNames[relation], indexFileNames[relation], inputRelations[relation], stringSizes[relation], inputRelations[relation].length, inputRelations[relation].length, tProjection, expr, joinColumns[relation]+1, false);
				Tuple tempTuple = tempIndex.get_next();
				RID temprid=new RID();
				while(tempTuple!=null){
					temprid = ConstantVars.getGlobalRID();
					if(tuplesMatch(tuple,tempTuple,inputRelations[relation]))
						break;
					tempTuple = tempIndex.get_next();
				}
				if(tempTuple!=null){
					RID superRID = new RID();
					superRID.pageNo=temprid.pageNo;
					superRID.slotNo=temprid.slotNo;
					if(topkMinSum[relation]<tempTuple.getFloFld(inputRelations[relation].length-1)){
						deleteFromKTuples(relation,temprid);
					}
					deleteFromInterFile(superRID,relation);
				}
			}
			if(outFile.getRecCnt() < knumberOfTuples){
				//outFile.
				writeTopK();
			   get_topK();
			}
			else if(outFile.getRecCnt()==knumberOfTuples)
				get_topK();
		}
		catch(Exception e){
			System.out.println("Error in deleteTuple");
			e.printStackTrace();
		}
	}
	
	private void initializeBTreeFileInter(){
		try{
			interBTF =new BTreeFile[numberOfTables];
			interIndexType = new IndexType[numberOfTables];
			interIndexName = new String[numberOfTables];
			interFileName = new String[numberOfTables];
			for(int i=0;i<numberOfTables;i++){
				interBTF[i] = new BTreeFile("interTATuples" + i +"_BTreeIndex", AttrType.attrString ,20,1);
				interIndexType[i] = new IndexType(IndexType.B_Index);
				interIndexName[i] = "interTATuples" + i + "_BTreeIndex";
				interFileName[i] = "TempResults.in";
			}

			Scan s = new Scan(tempFile);
			Tuple temp = null;
			RID rid1 = new RID();
			temp = s.getNext(rid1);
			Tuple t = new Tuple();
			t.setHdr((short)combinedAttrCount,combinedAttr,combinedStrSizes);
			while(temp!=null){
				for(int i=0;i<numberOfTables;i++){
					int column = getTupleOffset(i)+inputRelations[i].length-1;
					temp.setHdr((short)(combinedAttrCount),combinedAttr,combinedStrSizes);
					String strKey = temp.getStrFld(column);
					interBTF[i].insert(new StringKey(strKey), rid1);
				}
				temp = s.getNext(rid1);
			}
			s.closescan();
		}
		catch(Exception e){
			System.out.println("Exception in initializeBTreeFile");
			e.printStackTrace();
		}
	}
	private void deleteFromInterFile(RID delRID, int relation){
		try{
			String rid = delRID.pageNo.pid +"_"+ delRID.slotNo;
			int colNum = getTupleOffset(relation) + inputRelations[relation].length-1;
			int attrCount = combinedAttrCount;
			FldSpec[] tProjection = new FldSpec[attrCount];
			for (int i = 0; i < attrCount; i++)
				tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);

			CondExpr[] expr = new CondExpr[2];
			expr[0] = new CondExpr();
			expr[0].op = new AttrOperator(AttrOperator.aopEQ);
			expr[0].type1 = new AttrType(AttrType.attrSymbol);
			expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), colNum);
			expr[0].type2 = new AttrType(AttrType.attrString);
			expr[0].operand2.string = rid;			
			expr[0].next = null;
			expr[1] = null;
			
			IndexScan interIndexScan = new IndexScan(new IndexType(IndexType.B_Index),"TempResults.in",interIndexName[relation],combinedAttr,combinedStrSizes,combinedAttrCount,combinedAttrCount,tProjection,expr,colNum,false);
			Tuple delTuple = interIndexScan.get_next();
			while(delTuple!=null){
				RID tempRID = ConstantVars.getGlobalRID();
				String ridKey = delTuple.getStrFld(inputRelations[relation].length);
				float delScore = delTuple.getFloFld(inputRelations[relation].length-1);
				int fieldCount = 0;
				for(int r=getTupleOffset(relation);r<getTupleOffset(relation+1);r++){
					switch(inputRelations[relation][fieldCount].attrType){
					case AttrType.attrInteger:
						delTuple.setIntFld(r, 0);
						break;
					case AttrType.attrString:
						delTuple.setStrFld(r, "");
						break;
					case AttrType.attrReal:
						delTuple.setFloFld(r, 0.0f);
						break;
					}
					fieldCount++;
				}
				delTuple.setStrFld(inputRelations[relation].length,"");
				delTuple.setFloFld(combinedAttrCount-2, 0.0f);
				if(emptyTuple(delTuple,combinedAttr,joinColumns)){
					tempFile.deleteRecord(tempRID);
					interBTF[relation].Delete(new StringKey(ridKey), tempRID);
				}
				else{
					tempFile.updateRecord(tempRID, delTuple);
				}
				delTuple = interIndexScan.get_next();
			}
		}
		catch(Exception e){
			System.out.println("Error in deleteFromInterFile");
			e.printStackTrace();
		}
	}
	
	private boolean emptyTuple(Tuple tuple,AttrType[] tupAttrTypes, int[] joiningOn){
		boolean returnVal = true;
		try{
			AttrType keyType = tupAttrTypes[joiningOn[0]];
			for(int i=0;i<joiningOn.length;i++){
				switch(keyType.attrType){
				case AttrType.attrInteger:
					if(tuple.getIntFld(getTupleOffset(i))!=0)
						returnVal=false;
					break;
				case AttrType.attrString:
					if(!tuple.getStrFld(getTupleOffset(i)).equals(""))
						returnVal=false;
					break;
				}
			}
			return returnVal;
		}
		catch(Exception e){
			System.out.println("Exception in emptyTuple");
			e.printStackTrace();
			return false;
		}
	}
	private void deleteFromKTuples(int relation,RID temprid){
		try{
			String RIDVal = temprid.pageNo.pid+"_"+ temprid.slotNo;
			Scan fs = new Scan(outFile);
			RID rid = new RID();
			Tuple delTuple = fs.getNext(rid);
			while(delTuple!=null){
				delTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
				if(delTuple.getStrFld(getTupleOffset(relation)+inputRelations[relation].length-1).equals(RIDVal)){
					outFile.deleteRecord(rid);
				}
				delTuple = fs.getNext(rid);
			}
			fs.closescan();
		}
		catch(Exception e){
			System.out.println("Exception in deleteFromKTuples");
			e.printStackTrace();
		}
	}
	private boolean tuplesMatch(Tuple t1, Tuple t2, AttrType[] tupleAttrs){
		boolean flag=true;
		try{
			for(int i=0;i<tupleAttrs.length-1;i++){
				switch(tupleAttrs[i].attrType){
				case AttrType.attrInteger:
					if(t1.getIntFld(i+1)!=t2.getIntFld(i+1))
						return false;
					break;
				case AttrType.attrString:
					if(!t1.getStrFld(i+1).equals(t2.getStrFld(i+1)))
						return false;
					break;
				case AttrType.attrReal:
					if(t1.getFloFld(i+1)!=t2.getFloFld(i+1))
						return false;
					break;
				}
			}
			return flag;
		}
		catch(Exception e){
			System.out.println("Exception in tuplesMatch");
			e.printStackTrace();
			return flag;
		}
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
	
	public void calculateIndicator1()
	{
		int[] M = new int[this.numberOfTables];
		indicators = new float[numberOfTables];
		FldSpec[] fldProjectionList = new FldSpec[combinedAttrCount];
		//FldSpec[] fldProjectionList = new FldSpec[combinedAttrCount];
		for (int j = 0; j < fldProjectionList.length; j++) {
			fldProjectionList[j] = new FldSpec(new RelSpec(RelSpec.outer), j + 1);
		}
		try {
			float[] prevScore = new float[this.numberOfTables];
			float[] currScore = new float[this.numberOfTables];
			/*System.out.println("In Indicator Function");
			System.out.println("--------------------------------");
			printTempFile();
			System.out.println("--------------------------------");*/
			Tuple tempTuple;
			// Reset M.
			for (int j = 0; j < numberOfTables; j++) {
				M[j] = 0;
			}
			FileScan fScan = null;
			try {
				fScan = new FileScan("InterTuple.in", combinedAttr, combinedStrSizes,(short)combinedAttrCount, combinedAttrCount,combinedProjection, null);
						//new FileScan("TempResults.in", combinedAttr,combinedStrSizes, (short) combinedAttrCount,combinedAttrCount, combinedProjection, null);
				
			} catch (Exception ex) {
				ex.printStackTrace();
			}
			TupleOrder order = new TupleOrder(TupleOrder.Descending);
			Iterator topIterator = null;
			try {
				topIterator = new Sort(combinedAttr,(short) combinedAttrCount, combinedStrSizes, fScan,combinedAttrCount-1, order, 4, 20);				  
				
			} catch (SortException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			int count = knumberOfTuples;
			while ((tempTuple = topIterator.get_next()) != null) {
				if(count <= 1)
					break;
				int numTables=0;
				for(int j=0;j<numberOfTables;j++){
					if(tempTuple.getStrFld(joinColumns[j]+getTupleOffset(j)+1)!=null){
						numTables++;
					}					
				}
				int fieldLength = numTables;
				if(fieldLength == numberOfTables)
					continue;
				count--;
				Tuple tempStreamTuple = new Tuple();
				tempStreamTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
				tempStreamTuple.tupleCopy(tempTuple);
				//tempStreamTuple.print(interAttr);
				int sum = 0;
				for (int j = 0; j < numberOfTables; j++) {
					AttrType type = inputRelations[j][joinColumns[j]];
					//int fieldIndex = getTupleOffset(j);
					int fieldIndex = getTupleOffset(j)+joinColumns[j]+1;
					int flag =-1;
					switch(type.attrType)
					{
					case AttrType.attrInteger : 

						if(tempStreamTuple.getIntFld(fieldIndex) == 0)
							flag =0;
						else 
							flag =1;
						break;
					case AttrType.attrString :
						if(tempStreamTuple.getStrFld(fieldIndex).equals(""))
							flag =0;
						else
							flag =1;
						break;
					case AttrType.attrReal :
						if(tempStreamTuple.getFloFld(fieldIndex) == 0)
							flag =0;
						else
							flag =1;
						break;
					}
					if (flag == 0) {
						M[j]++;
					} 
					else {
						sum++;
					}
				}
			}
			//topIterator.close();
			fScan.close();
			FileScan fileScan =
					new FileScan("TempResults.in",combinedAttr, combinedStrSizes, (short) combinedAttrCount,combinedAttrCount, fldProjectionList, null);
			
			while ((tempTuple = fileScan.get_next()) != null) {
				
				Tuple tempStreamTuple = new Tuple();
				tempStreamTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
				tempStreamTuple.tupleCopy(tempTuple);
				//tempStreamTuple.print(interAttr);
				//tempStreamTuple.print(combinedAttr);
				for (int j = 0; j < numberOfTables; j++) {
					int flag = -1;
					AttrType type = inputRelations[j][joinColumns[j]];
					int fieldIndex = getTupleOffset(j)+joinColumns[j]+1;
					//int fieldIndex = getTupleOffset(j);
					switch(type.attrType)
					{
					case AttrType.attrInteger : 

						if(tempStreamTuple.getIntFld(fieldIndex) == 0)
							flag =0;
						else 
							flag =1;
						break;
					case AttrType.attrString :
						if(tempStreamTuple.getStrFld(fieldIndex).equals(""))
							flag =0;
						else
							flag =1;
						break;
					case AttrType.attrReal :
						if(tempStreamTuple.getFloFld(fieldIndex) == 0)
							flag =0;
						else
							flag =1;
						break;
					}
					if (flag !=0) {
						prevScore[j] = currScore[j];
						float score = tempStreamTuple.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
						currScore[j] = score;
					}
				}
			}
			fileScan.close();
			// Stream combine variables.
			float dervOfAvgFunc = (float) (1.0f / numberOfTables);
			// Calculate the indicators for each stream.
			for (int i = 0; i < numberOfTables; i++) {
				double diff = (double) prevScore[i] - currScore[i];	
				indicators[i] = (float) (M[i] * dervOfAvgFunc * diff);
			}
		} 
		catch (Exception e) {

			e.printStackTrace();
		}
	}
	
	private int checkIndicator()
	{
		calculateIndicator1();
		boolean temp = false;
		float maxIndicator=-1;
		float indicator =-1;
		int tableIndex =-1;
		for(int i=0;i<numberOfTables;i++){
			indicator = indicators[i];
			if(indicator>maxIndicator)
			{
				maxIndicator = indicator;
				tableIndex =i;
			}
		}
		arr[tableIndex]++;
		for(int i=0;i<numberOfTables;i++){
			if(arr[i]>=numberOfTables)
			{
				if(i==numberOfTables-1)
					tableIndex =0;
				else
					tableIndex =i+1;
				temp =true;
				break;
			}
			
		}
		if(temp){
			for(int i=0;i<numberOfTables;i++){
				arr[i]=0;
			}
			temp =false;
		}
		return tableIndex;
	}
	
	

}