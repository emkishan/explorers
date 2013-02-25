package iterator;

import global.AttrOperator;
import global.AttrType;
import global.IndexType;
import global.RID;
import global.TupleOrder;
import heap.FieldNumberOutOfBoundException;
import heap.HFBufMgrException;
import heap.HFDiskMgrException;
import heap.HFException;
import heap.Heapfile;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Scan;
import heap.Tuple;
import index.IndexException;
import index.IndexScan;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import bufmgr.PageNotReadException;

public class TopRankJoin extends Iterator {

	private int numberOfTables;
	private AttrType inputRelations[][];
	private int lengths[];
	private short[][] stringSizes;
	private int joinColumns[];
	private Iterator iterators[];
	private IndexType indexes[];
	private String[] indexNames[];
	private CondExpr[] outFilter;
	private int knumberOfTuples;
	private FldSpec[] proj_list;
	private int rank;
	private Tuple innerTuples[];
	private int n_buf_pgs;
	private int numOutputFlds;
	private Tuple JTuple;
	private int numOfScanned[], numOfProbed[];
	private Heapfile heapFiles[], outFile;
	private RID fileRid;
	private boolean firstTime;
	private String[] indexFileNames;
	private HashMap<Integer, ArrayList<ArrayList<RIDScore>>> ridScore = new HashMap<Integer, ArrayList<ArrayList<RIDScore>>>();
	private HashMap<Integer, ArrayList<ArrayList<Integer>>> relationsVisited = new HashMap<Integer, ArrayList<ArrayList<Integer>>>();

	TopRankJoin(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			IndexType[] index, java.lang.String[] indNames, int amt_of_mem,
			CondExpr[] outFilter, FldSpec[] proj_list, int n_out_flds, int num,
			int rank) throws IOException, TopRankJoinException {

		numberOfTables = numTables;
		inputRelations = new AttrType[numTables][];
		indexFileNames = indNames;
		outFile = null;
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

		// Copy the attribute types

		for (int i = 0; i < numTables; i++) {
			lengths[i] = len_in[i];
			inputRelations[i] = new AttrType[len_in[i]];
			System.arraycopy(inputRelations[i], 0, in[i], 0, len_in[i]);
		}

		// Copy the iterators

		for (int i = 0; i < numTables; i++) {
			iterators[i] = am[i];
		}

		innerTuples = new Tuple[numTables];

		// Copy the String sizes and initialize tuples
		for (int i = 0; i < numTables; i++) {
			stringSizes[i] = s_sizes[i];
			innerTuples[i] = new Tuple();
		}

		JTuple = new Tuple();
		n_buf_pgs = amt_of_mem;
		rank = rank;
		numOutputFlds = n_out_flds;
		knumberOfTuples = num;

		AttrType[] Restypes = new AttrType[n_out_flds];

		// Copy projection list and conditions
		// Initialize scanned and probed counters
		numOfProbed = new int[numTables];
		numOfScanned = new int[numTables];
		for (int i = 0; i < numTables; i++) {
			this.outFilter[i] = outFilter[i];
			this.proj_list[i] = proj_list[i];
			numOfProbed[i] = 0;
			numOfScanned[i] = 0;
		}

		try {
			TupleUtils.setup_op_tuple(JTuple, Restypes, inputRelations, len_in,
					s_sizes, proj_list, n_out_flds);
		} catch (TupleUtilsException e) {
			throw new TopRankJoinException(e,
					"TupleUtilsException caught by TopRankJoin");
		} catch (IOException e) {
			throw new TopRankJoinException(e,
					"IOException caught by TopRankJoin");
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

	private void createTopKTuples() {
		Tuple tuple = new Tuple();
		RID rid = new RID();
		int count = 0;
		AttrType attrType = new AttrType(
				inputRelations[0][joinColumns[0]].attrType);
		Scan fileScans[] = new Scan[numberOfTables];
		try {
			for (int i = 0; i < numberOfTables; i++)
				fileScans[i] = heapFiles[i].openScan();
			while (count < knumberOfTuples) {
				for (int i = 0; i < numberOfTables; i++) {
					tuple = fileScans[i].getNext(rid);
					switch (attrType.attrType) {
					case AttrType.attrInteger:
						int key = tuple.getIntFld(joinColumns[i]);
						RIDScore newRid = new RIDScore(rid, tuple.getScore());
						if (ridScore.containsKey(key)) {
							// ArrayList<ArrayList<RIDScore>> scoresArray =ridScore.get(key);
							if (relationsVisited.containsKey(key)) {
								if (relationsVisited.get(key) != null) {
									ArrayList<Integer> relations = relationsVisited.get(key).get(0);
									ArrayList<RIDScore> ridRelations = ridScore.get(key).get(0);
									boolean flag = false;
									for (int relationIndex = 0; relationIndex < relations.size(); relationIndex++) {
										if (i == relations.get(relationIndex)) {
											// Add relations to the hashMap
											ArrayList<Integer> newRelation = relations;
											relationsVisited.get(key).add(newRelation);
											flag = true;

											// Add RIDScore to hashMap with new RID
											ArrayList<RIDScore> ridRelation = ridRelations;
											ridRelation.add(i, newRid);
											ridScore.get(key).add(ridRelation);

											// break the loop once the relation and newRID is set
											break;
										}
									}
									if (flag == false) {
										// if the relation does not exists then
										// add to the array of relations
										for (int index = 0; index < relationsVisited.get(key).size(); index++) {
											// Add new Relation to the HashMap
											ArrayList<Integer> rel = relationsVisited.get(key).get(index);
											rel.add(i);
											relationsVisited.get(key).add(rel);

											// Add new RIDScore to the HashMap
											ArrayList<RIDScore> ridRel = ridScore.get(key).get(index);
											ridRel.add(newRid);
											ridScore.get(key).add(ridRel);
										}
									}
								}
							} else {
								// Create a new ArrayList to insert relations if
								// the key does not exists
								ArrayList<Integer> relations = new ArrayList<Integer>();
								relations.add(i);
								ArrayList<ArrayList<Integer>> temp = new ArrayList<ArrayList<Integer>>();
								temp.add(relations);
								relationsVisited.put(key, temp);

								// Create a new ArrayList to insert RIDScore if
								// the key does not exists
								ArrayList<RIDScore> ridArray = new ArrayList<RIDScore>();
								ridArray.add(newRid);
								ridScore.get(key).add(ridArray);
							}
						}
						count++;

						break;
					case AttrType.attrReal:
						HashMap<Float, ArrayList<ArrayList<RIDScore>>> ridScoreF = new HashMap<Float, ArrayList<ArrayList<RIDScore>>>();
						HashMap<Float, ArrayList<ArrayList<Integer>>> relationsVisitedF = new HashMap<Float, ArrayList<ArrayList<Integer>>>();
						// ridScore = new HashMap<Float, ArrayList<RIDScore>>();
						// relationsVisited = new HashMap<Float,
						// ArrayList<Integer>>();
						break;
					case AttrType.attrString:
						// ridScore = new HashMap<String,
						// ArrayList<RIDScore>>();
						// relationsVisited = new HashMap<String,
						// ArrayList<Integer>>();
						break;
					}// end of switch
				}//end of for
			}//end of while
			IndexScan iscan[] = new IndexScan[numberOfTables];
			Set<Integer> keySet = relationsVisited.keySet();
			for(java.util.Iterator<Integer> it = keySet.iterator(); it.hasNext(); ){
					Integer visitKey = it.next();
					ArrayList<Integer> relArray = relationsVisited.get(visitKey).get(0);
					if(relArray.size()!=numberOfTables){
						
							for(int tableNum=0; tableNum<numberOfTables;tableNum++){
								boolean relFlag = false;
								for(int notVisit=0;notVisit<relArray.size();notVisit++){
									if(relArray.get(notVisit)==tableNum){
										relFlag = true;
										break;
									}
								}
								if(!relFlag){
									int attrLength = inputRelations[tableNum].length;
									//create projectionList for Index Scan
									 FldSpec [] Sprojection = new FldSpec[attrLength];
									 for(int attr=0; attr<attrLength; attr++){
										 Sprojection[attr]= new FldSpec(new RelSpec(RelSpec.outer), attr+1);
									 }
									 
									 //create condition for Index Scan
									 CondExpr[] expr = new CondExpr[2];
									    expr[0] = new CondExpr();
									    expr[0].op = new AttrOperator(AttrOperator.aopEQ);
									    expr[0].type1 = new AttrType(AttrType.attrSymbol);
									    expr[0].type2 = new AttrType(AttrType.attrString);
									    expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[tableNum]);
									    expr[0].operand2.integer = visitKey;
									    expr[0].next = null;
									    expr[1] = null;
									 //Index Scan
									iscan[tableNum] = new IndexScan(new IndexType(IndexType.B_Index), indexFileNames[tableNum], "BTreeIndex", inputRelations[tableNum], stringSizes[tableNum], attrLength, attrLength, Sprojection, expr, joinColumns[tableNum], false);
									
									RID newRid = new RID();
									Tuple t = iscan[tableNum].get_next(newRid);
									RIDScore rScore = new RIDScore(newRid, t.getScore());
									for (int index = 0; index < relationsVisited.get(visitKey).size(); index++) {
										// Add new Relation to the HashMap
										ArrayList<Integer> rel = relationsVisited.get(visitKey).get(index);
										rel.add(tableNum);
										relationsVisited.get(visitKey).add(rel);

										// Add new RIDScore to the HashMap
										ArrayList<RIDScore> ridRel = ridScore.get(visitKey).get(index);
										ridRel.add(rScore);
										ridScore.get(visitKey).add(ridRel);
									}
								}
						}
					}
				}
			
			//Projection List
			for(java.util.Iterator it = ridScore.keySet().iterator(); it.hasNext();){
				int mainKey = (int)it.next();
				ArrayList<ArrayList<RIDScore>> value = ridScore.get(mainKey);
				Tuple outTuple = new Tuple();
				AttrType[] Restypes = new AttrType[numOutputFlds];
				short[] t_size= TupleUtils.setup_op_tuple(outTuple, Restypes, inputRelations, lengths,
						stringSizes, proj_list, numOutputFlds);
				
				for(int index=0; index<value.size();index++){
					ArrayList<RIDScore> ridArray = value.get(index);
					Float score = 0.0f;
					for(int k=0;k<ridArray.size();k++){
						RIDScore ridObj = ridArray.get(k);
						RID newRid = ridObj.getRid();
						int relIndex = relationsVisited.get(mainKey).get(index).get(k);
						Tuple currentTuple = heapFiles[relIndex].getRecord(newRid);
						score += currentTuple.getScore();
						for(int proj=0;proj<proj_list.length;proj++){
							FldSpec spec = proj_list[proj];
							int offset = spec.offset;
							AttrType attr = inputRelations[relIndex][offset-1];
							//Write to the tuple using projList
							if(relIndex==spec.relation.key){
								switch(attr.attrType){
								case AttrType.attrInteger:
									outTuple.setIntFld(proj+1, currentTuple.getIntFld(offset));
									break;
								case AttrType.attrReal:
									outTuple.setFloFld(proj+1, currentTuple.getFloFld(offset));
									break;
								case AttrType.attrString:
									outTuple.setStrFld(proj+1, currentTuple.getStrFld(offset));
									break;
								}
							}
						}
						score = score/numberOfTables;
						outTuple.setScore(score);
						int attrSizes = outTuple.attrSizes;
						
						//set final tuple attribute types for finalTuple to include score
						Tuple finalTuple = new Tuple();
						AttrType[] outAttrTypes = outTuple.attr_Types;
						AttrType[] attrArray = new AttrType[attrSizes+1];
						for(int attrIndex=0;attrIndex<attrArray.length;attrIndex++){
							attrArray[attrIndex] = outAttrTypes[attrIndex];
						}
						attrArray[attrSizes] = new AttrType(AttrType.attrReal);
						//set final Tuple header
						finalTuple.setHdr((short) (outTuple.noOfFlds() + 1), attrArray,outTuple.string_sizes);
						//copy the tuple
						writeTuple(outTuple, finalTuple);
						//write to a new file all the results
						fileRid = outFile.insertRecord(finalTuple.getTupleByteArray());
						
					}
					
				}
				
			}
		}// end of try
		catch (Exception e) {
			System.out.println("Exception in createTopKTuples");
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
	
	//Write to a new Tuple to add score as a field
	public void writeTuple(Tuple inputTuple, Tuple OutTuple)
			throws UnknowAttrType, WrongPermat, FieldNumberOutOfBoundException,
			IOException {
		int nOutFlds = inputTuple.attr_Types.length;
		for (int i = 0; i < nOutFlds; i++) {
			switch (inputTuple.attr_Types[i].attrType) {
			case AttrType.attrInteger:
				OutTuple.setIntFld(i + 1, inputTuple.getIntFld(i + 1));
				break;
			case AttrType.attrReal:
				OutTuple.setFloFld(i + 1, inputTuple.getFloFld(i + 1));
				break;
			case AttrType.attrString:
				OutTuple.setStrFld(i + 1, inputTuple.getStrFld(i + 1));
				break;
			default:
				throw new UnknowAttrType(
						"Don't know how to handle attrSymbol, attrNull");
			}
		}
		OutTuple.setFloFld(nOutFlds + 1, inputTuple.getScore());
		return;
	}
	
	public void get_topK(String inputFile, Tuple outTuple) {
		short attrLength = (short)outTuple.attr_Types.length;
		FldSpec[] tProjection = new FldSpec[attrLength];
		for (int i = 0; i < attrLength; i++)
			tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
		FileScan fm1 = null;
		try {
			fm1 = new FileScan(inputFile, outTuple.attr_Types, outTuple.string_sizes,
					attrLength, attrLength,
					tProjection, null);
		} catch (FileScanException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (TupleUtilsException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvalidRelation e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		TupleOrder order = new TupleOrder(rank);
		Iterator topIterator = null;
		try {
			
			topIterator = new Sort(outTuple.attr_Types,attrLength,
					outTuple.string_sizes, fm1, outTuple.attrSizes, order, 4, n_buf_pgs);
		} catch (SortException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple tuple1;
		int topK = knumberOfTuples;
		while (topK > 0) {
			try {
				if ((tuple1 = topIterator.get_next()) != null) {
					tuple1.print(outTuple.attr_Types);
				}
				topK--;
			} catch (JoinsException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IndexException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InvalidTupleSizeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InvalidTypeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (PageNotReadException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (TupleUtilsException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (PredEvalException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (SortException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (LowMemException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (UnknowAttrType e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (UnknownKeyTypeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

	}
}