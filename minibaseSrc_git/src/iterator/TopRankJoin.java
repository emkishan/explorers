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
import java.util.HashSet;
import java.util.Set;

import btree.BTreeFile;
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
			short[][] s_sizes, int[] join_col_in, Iterator[] am,RelSpec relSpec,
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
	
	private boolean validTuple(Tuple tempTuple,int relationNumber){
		boolean returnValue = true;
		try{
			for(int i=0;i<outFilter.length;i++){
				AttrType left = outFilter[i].type1;
				FldSpec operand1Sym = outFilter[i].operand1.symbol;
				int colNo = operand1Sym.offset;
				int relNo = operand1Sym.relation.key;
				if(relNo == relationNumber){
					switch(left.attrType){
					case AttrType.attrInteger:
						int rightPart = outFilter[i].operand2.integer;
						int leftInt = tempTuple.getIntFld(colNo);
						switch(outFilter[i].op.attrOperator){
						case AttrOperator.aopEQ:
							if(rightPart==leftInt)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGE:
							if(leftInt >= rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGT:
							if(leftInt > rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLE:
							if(leftInt <= rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLT:
							if(leftInt < rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopNE:
							if(leftInt != rightPart)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						}
						break;
					case AttrType.attrReal:
						float rightFloat = outFilter[i].operand2.real;
						float leftFloat = tempTuple.getFloFld(colNo);
						switch(outFilter[i].op.attrOperator){
						case AttrOperator.aopEQ:
							if(leftFloat==rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGE:
							if(leftFloat >= rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopGT:
							if(leftFloat > rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLE:
							if(leftFloat <= rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopLT:
							if(leftFloat < rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						case AttrOperator.aopNE:
							if(leftFloat != rightFloat)
								returnValue = returnValue && true;
							else
								returnValue = false;
							break;
						}
						break;
					case AttrType.attrString:
						String rightString = outFilter[i].operand2.string;
						String leftString = tempTuple.getStrFld(colNo);
						if(rightString != leftString)
							returnValue = returnValue && true;
						else
							returnValue = false;
						break;
					}
				}
			}
		}
		catch(Exception e){
			System.out.println("Exception while processing Tuple in Top Rank Join");
		}
		return returnValue;
	}

	private void createTopKTuples() {
		Tuple tuple = new Tuple();
		RID rid = new RID();
		int count = 0;
		Tuple interTuple = new Tuple();
		int attrCount=0;
		int strSizesCount=0;
		int attrIndex = 0;
		int strCount = 0;
		AttrType attrType = new AttrType(inputRelations[0][joinColumns[0]].attrType);
		Scan fileScans[] = new Scan[numberOfTables];
		
		//get Attribute count
		for(int i=0;i<inputRelations.length;i++){
			attrCount+=inputRelations[i].length;
		}
		FldSpec[] tProjection = new FldSpec[attrCount];
		for (int i = 0; i < attrCount; i++)
			tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
		//get string sizes count
		AttrType[] interAttr = new AttrType[attrCount];
		for(int i =0;i<stringSizes.length;i++){
			for(int j=0;j<stringSizes[i].length;j++){
				strCount++;
			}
		}
		short[] strSizes = new short[strCount];
		int strIndex =0;
		//get string sizes for intermediate tuple
		for(int i =0;i<stringSizes.length;i++){
			for(int j=0;j<stringSizes[i].length;j++){
				strSizes[strIndex++]=stringSizes[i][j];
			}
		}
		//get attribute types for intermediate tuple
		for(int i=0;i<inputRelations.length;i++){
			for(int j=0;j<inputRelations[i].length;j++){
				interAttr[attrIndex] = inputRelations[i][j];
				
			}
		}
		//create intermediate tuple header
		interTuple.setHdr((short)attrCount, interAttr, strSizes);
		Heapfile interFile = new Heapfile("InterTuple.in");
		BTreeFile btf = null;
		int keysize =4;
		int strKeyCount = 0;
		if(attrType.attrType ==AttrType.attrString){
			for(int i=0;i<inputRelations[0].length;i++){
				if(inputRelations[0][i].attrType == AttrType.attrString){
					if(i==joinColumns[0]){
						keysize = stringSizes[0][strKeyCount];
						break;
					}
					else{
						strKeyCount++;
					}
				}
				
		}
			
		btf = new BTreeFile("BtreeIndex", attrType.attrType, keysize, 1);	
		IndexScan interScan = null;
		try {
			for (int i = 0; i < numberOfTables; i++)
				fileScans[i] = heapFiles[i].openScan();
			while (count < knumberOfTuples) {
				for (int i = 0; i < numberOfTables; i++) {
					tuple = fileScans[i].getNext(rid);
					if(validTuple(tuple,i)){
					switch (attrType.attrType) {
					case AttrType.attrInteger:
						int key = tuple.getIntFld(joinColumns[i]);
						
						interTuple.setIntFld(key, joinColumns[0]);
							if (relationsVisited.containsKey(key)) {
								if (relationsVisited.get(key) != null) {
									ArrayList<Integer> relations = relationsVisited.get(key).get(0);
									boolean flag = false;
									for (int relationIndex = 0; relationIndex < relations.size(); relationIndex++) {
										if (i == relations.get(relationIndex)) {
											// Add relations to the hashMap
											ArrayList<Integer> newRelation = relations;
											relationsVisited.get(key).add(newRelation);
											flag = true;
											int tupleOffset = getTupleOffset(i);
											CondExpr[] condExpr = getConditionExp(i);
											for(int exprIndex=0;exprIndex<condExpr.length;exprIndex++){
												CondExpr conObject = condExpr[exprIndex];
												if(conObject.operand2.symbol!=null){
													FldSpec fSpec1 = conObject.operand1.symbol;
													FldSpec fSpec2 = conObject.operand2.symbol;
													if(fSpec1.relation.key==i){
														if(relations.contains(fSpec2.relation.key)){
															CondExpr[] expr = new CondExpr[1];
														    expr[0] = new CondExpr();
														    expr[0].op = new AttrOperator(AttrOperator.aopEQ);
														    expr[0].type1 = new AttrType(AttrType.attrSymbol);
														    expr[0].type2 = new AttrType(AttrType.attrString);
														    expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]);
														    expr[0].operand2.integer = key;
														    expr[0].next = null;
														    expr[1] = null;
															
														    interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0], false);
														    Tuple t = new Tuple();
														    t.setHdr((short)attrCount, interAttr, strSizes);
														    RID newRid = new RID();
														    while((t = interScan.get_next(newRid))!=null){
														    	//get offset number of that tuple in interTuple
														    	int offset = getTupleOffset(fSpec2.relation.key)+fSpec2.offset;
														    	boolean evalCondition = true;
														    	switch((inputRelations[fSpec2.relation.key][offset-1]).attrType){
														    	
														    	case AttrType.attrInteger:
														    		evalCondition = evaluateCondition(tuple.getIntFld(fSpec1.offset),t.getIntFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
														    		
														    		//Condition evaluates to true so update the tuple
														    		if(evalCondition){
														    			updateTuple(tuple, t, i, tupleOffset);
														    			interFile.updateRecord(newRid, t);
														    		}
														    		else{
														    			//condition fails so add the tuple as new Record in heap file
														    			Tuple newTuple = new Tuple();
														    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
														    			updateTuple(tuple,newTuple, i, tupleOffset);
														    			interFile.insertRecord(newTuple.getTupleByteArray());
														    		}
														    		break;
														    	case AttrType.attrReal:
														    		evalCondition = evaluateCondition(tuple.getFloFld(fSpec1.offset),t.getFloFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
														    		//Condition evaluates to true so update the tuple
														    		if(evalCondition){
														    			updateTuple(tuple, t, i, tupleOffset);
														    			interFile.updateRecord(newRid, t);
														    		}
														    		else{
														    			//condition fails so add the tuple as new Record in heap file
														    			Tuple newTuple = new Tuple();
														    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
														    			updateTuple(tuple,newTuple, i, tupleOffset);
														    			interFile.insertRecord(newTuple.getTupleByteArray());
														    		}
														    		break;
														    		
														    	case AttrType.attrString:
														    		evalCondition = evaluateCondition(tuple.getStrFld(fSpec1.offset),t.getStrFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
														    		//Condition evaluates to true so update the tuple
														    		if(evalCondition){
														    			updateTuple(tuple, t, i, tupleOffset);
														    			interFile.updateRecord(newRid, t);
														    		}
														    		else{
														    			//condition fails so add the tuple as new Record in heap file
														    			Tuple newTuple = new Tuple();
														    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
														    			updateTuple(tuple,newTuple, i, tupleOffset);
														    			interFile.insertRecord(newTuple.getTupleByteArray());
														    		}
														    		break;
														    	}
														    }
														}
														else{
															//write tuple to the file
															Tuple newTuple = new Tuple();
											    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
											    			updateTuple(tuple,newTuple, i, tupleOffset);
											    			newTuple.setIntFld(joinColumns[0], key);
											    			interFile.insertRecord(newTuple.getTupleByteArray());
														}
													}
													else if(fSpec2.relation.key==i){
															if(relations.contains(fSpec1.relation.key)){
																CondExpr[] expr = new CondExpr[1];
															    expr[0] = new CondExpr();
															    expr[0].op = new AttrOperator(AttrOperator.aopEQ);
															    expr[0].type1 = new AttrType(AttrType.attrSymbol);
															    expr[0].type2 = new AttrType(AttrType.attrString);
															    expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]);
															    expr[0].operand2.integer = key;
															    expr[0].next = null;
															    expr[1] = null;
																
															    interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0], false);
															    Tuple t = new Tuple();
															    t.setHdr((short)attrCount, interAttr, strSizes);
															    RID newRid = new RID();
															    while((t = interScan.get_next(newRid))!=null){
															    	//get offset number of that tuple in interTuple
															    	int offset = getTupleOffset(fSpec1.relation.key)+fSpec1.offset;
															    	boolean evalCondition = true;
															    	switch((inputRelations[fSpec1.relation.key][offset-1]).attrType){
															    	
															    	case AttrType.attrInteger:
															    		evalCondition = evaluateCondition(tuple.getIntFld(fSpec2.offset),t.getIntFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
															    		
															    		//Condition evaluates to true so update the tuple
															    		if(evalCondition){
															    			updateTuple(tuple, t, i, tupleOffset);
															    			interFile.updateRecord(newRid, t);
															    			addKeyToRelations(key, i);
															    		}
															    		else{
															    			//condition fails so add the tuple as new Record in heap file
															    			Tuple newTuple = new Tuple();
															    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
															    			updateTuple(tuple,newTuple, i, tupleOffset);
															    			interFile.insertRecord(newTuple.getTupleByteArray());
															    		}
															    		break;
															    	case AttrType.attrReal:
															    		evalCondition = evaluateCondition(tuple.getFloFld(fSpec2.offset),t.getFloFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
															    		//Condition evaluates to true so update the tuple
															    		if(evalCondition){
															    			updateTuple(tuple, t, i, tupleOffset);
															    			interFile.updateRecord(newRid, t);
															    		}
															    		else{
															    			//condition fails so add the tuple as new Record in heap file
															    			Tuple newTuple = new Tuple();
															    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
															    			updateTuple(tuple,newTuple, i, tupleOffset);
															    			interFile.insertRecord(newTuple.getTupleByteArray());
															    		}
															    		break;
															    		
															    	case AttrType.attrString:
															    		evalCondition = evaluateCondition(tuple.getStrFld(fSpec2.offset),t.getStrFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
															    		//Condition evaluates to true so update the tuple
															    		if(evalCondition){
															    			updateTuple(tuple, t, i, tupleOffset);
															    			interFile.updateRecord(newRid, t);
															    		}
															    		else{
															    			//condition fails so add the tuple as new Record in heap file
															    			Tuple newTuple = new Tuple();
															    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
															    			updateTuple(tuple,newTuple, i, tupleOffset);
															    			interFile.insertRecord(newTuple.getTupleByteArray());
															    			
															    		}
															    		break;
															    	}
															    }
															}
															else{
																//write tuple to the file
																Tuple newTuple = new Tuple();
												    			newTuple.setHdr((short)attrCount, interAttr, strSizes);
												    			updateTuple(tuple,newTuple, i, tupleOffset);
												    			newTuple.setIntFld(joinColumns[0], key);
												    			interFile.insertRecord(newTuple.getTupleByteArray());
															}
													}
													
												}
											}
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
						break;
					case AttrType.attrString:
						
						break;
					}// end of switch
					}//end of if
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
	
	private void createTupleHdr(Tuple tuple){
		FldSpec[] pList = proj_list;
		CondExpr[] oFilter = outFilter;
		int projLength = pList.length;
		ArrayList<AttrType> attrTypes = new ArrayList<AttrType>();
		ArrayList<Short> stringSizes = new ArrayList<Short>();
		Set<Integer> fldSet = new HashSet<Integer>();
		//To add projList attributes in out tuple
		for(int i=0;i<pList.length;i++){
			int relationIndex = pList[i].relation.key;
			int fieldOffset = pList[i].offset-1;
			attrTypes.add(inputRelations[relationIndex][fieldOffset]);
		}
		/*for(int i =0;i<numberOfTables;i++){
			
		}*/
		}
	private CondExpr[] getConditionExp(int tableIndex){
		ArrayList<CondExpr> condExp = new ArrayList<CondExpr>();
		for(int i=0;i<outFilter.length;i++){
			CondExpr tableCondition = outFilter[i];
			if(tableCondition.operand1.symbol.relation.key==tableIndex||tableCondition.operand2.symbol.relation.key==tableIndex){
				condExp.add(tableCondition);
			}
		}		
		return (CondExpr[])condExp.toArray();
	}
	
	private int getTupleOffset(int tableIndex){
		int offset = 0;
		for(int i=0;i<tableIndex;i++){
			offset+=inputRelations[i].length;
		}
		return offset;
		
	}
	
	private boolean evaluateCondition(Object obj1, Object obj2, AttrType attrType, AttrOperator attrOperator){
		boolean returnValue = true;
		switch(attrType.attrType){
		case AttrType.attrInteger:
			int leftInt = (Integer)obj1;
			int rightPart = (Integer)obj2;
			switch(attrOperator.attrOperator){
			case AttrOperator.aopEQ:
				if(rightPart==leftInt)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopGE:
				if(leftInt >= rightPart)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopGT:
				if(leftInt > rightPart)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopLE:
				if(leftInt <= rightPart)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopLT:
				if(leftInt < rightPart)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopNE:
				if(leftInt != rightPart)
					return returnValue;
				else
					return !returnValue;
			}
			break;
		case AttrType.attrReal:
			float leftFloat = (Float)obj1;
			float rightFloat = (Float)obj2;
			switch(attrOperator.attrOperator){
			case AttrOperator.aopEQ:
				if(rightFloat==leftFloat)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopGE:
				if(leftFloat >= rightFloat)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopGT:
				if(leftFloat > rightFloat)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopLE:
				if(leftFloat <= rightFloat)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopLT:
				if(leftFloat < rightFloat)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopNE:
				if(leftFloat != rightFloat)
					return returnValue;
				else
					return !returnValue;
			}
			break;
		case AttrType.attrString:
			String s1 = obj1.toString();
			String s2 = obj2.toString();
			switch(attrOperator.attrOperator){
			case AttrOperator.aopEQ:
				if(s1.equalsIgnoreCase(s2))
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopGE:
				if(s1.compareToIgnoreCase(s2)>=0)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopGT:
				if(s1.compareToIgnoreCase(s2)>0)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopLE:
				if(s1.compareToIgnoreCase(s2)<=0)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopLT:
				if(s1.compareToIgnoreCase(s2)<0)
					return returnValue;
				else
					return !returnValue;
			case AttrOperator.aopNE:
				if(!(s1.equalsIgnoreCase(s2)))
					return returnValue;
				else
					return !returnValue;
				
			}
			break;
		}
		return false;
	}
	
	private void updateTuple(Tuple inTuple,Tuple outTuple, int tableIndex, int offset){
		int fieldCount =1;
		for(int tField=1;tField<=inputRelations[tableIndex].length;tField++){
			switch(inputRelations[tableIndex][tField].attrType){
				case AttrType.attrInteger:
					try {
						outTuple.setIntFld(offset + 1,
								inTuple.getIntFld(fieldCount));
						fieldCount++;
					} catch (FieldNumberOutOfBoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					break;
				case AttrType.attrReal:
					try {
						outTuple.setFloFld(offset+1, inTuple.getFloFld(fieldCount));
						fieldCount++;
					} catch (FieldNumberOutOfBoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					break;
				case AttrType.attrString:
					try {
						outTuple.setStrFld(offset+1, inTuple.getStrFld(fieldCount));
						fieldCount++;
					} catch (FieldNumberOutOfBoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					break;
			}
		}
	}
	
	private void addKeyToRelations(int key, int tableIndex){
		for (int index = 0; index < relationsVisited.get(key).size(); index++) {
			// Add new Relation to the HashMap
			ArrayList<Integer> rel = relationsVisited.get(key).get(index);
			rel.add(tableIndex);
			relationsVisited.get(key).add(rel);											
		}
	}
}