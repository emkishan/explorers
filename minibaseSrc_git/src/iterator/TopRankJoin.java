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

import btree.AddFileEntryException;
import btree.BTreeFile;
import btree.ConstructPageException;
import btree.GetFileEntryException;
import btree.IntegerKey;
import btree.StringKey;
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
	private boolean duplFlag= false;
	private String[] fileNames;
	//private HashMap<Integer, ArrayList<ArrayList<RIDScore>>> ridScore = new HashMap<Integer, ArrayList<ArrayList<RIDScore>>>();
	private HashMap<Integer, ArrayList<ArrayList<Integer>>> relationsVisited = new HashMap<Integer, ArrayList<ArrayList<Integer>>>();
	private HashMap<String, ArrayList<ArrayList<Integer>>> sRelationsVisited = new HashMap<String, ArrayList<ArrayList<Integer>>>();
	private Tuple t = new Tuple();
	RID newRid = new RID();

	public TopRankJoin(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			IndexType[] index, java.lang.String[] indNames, int amt_of_mem,
			CondExpr[] outFilter, FldSpec[] proj_list, int n_out_flds, int num,
			int rank, String[] fileNames) throws IOException, TopRankJoinException {

		numberOfTables = numTables;
		inputRelations = new AttrType[numTables][];
		indexFileNames = indNames;
		joinColumns=join_col_in;
		outFile = null;
		iterators = am;
		this.fileNames =  fileNames;
		//System.out.println("iterators : "+iterators.length);
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
		
		if(duplFlag){
			
		}
		// Copy the attribute types
		lengths = new int[numTables];
		/*for (int i = 0; i < numTables; i++) {
			lengths[i] = len_in[i];
			inputRelations[i] = new AttrType[len_in[i]];
			System.arraycopy(inputRelations[i], 0, in[i], 0, len_in[i]);
		}*/
		
		for(int i=0;i<in.length;i++){
			inputRelations[i] = new AttrType[in[i].length];
			lengths[i] = len_in[i];
			for(int j=0;j<in[i].length;j++){
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
		//innerTuples = new
		for (int i = 0; i < numTables; i++) {
			stringSizes[i] = s_sizes[i];
			//innerTuples[i] = new Tuple();
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
		this.outFilter = new CondExpr[outFilter.length];
		this.proj_list = new FldSpec[proj_list.length];
		for (int i = 0; i < outFilter.length; i++) {
			this.outFilter[i] = outFilter[i];
			numOfProbed[i] = 0;
			numOfScanned[i] = 0;
		}
		
		for(int i=0;i<proj_list.length;i++){
			this.proj_list[i] = proj_list[i];
		}
		
		try {
			TupleUtils.setup_op_tuple(JTuple, Restypes, in, len_in,
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
		createTopKTuples();
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
				AttrType left = outFilter[i].type2;
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
					switch(outFilter[i].op.attrOperator){	
					case AttrOperator.aopEQ:
						if(leftString.equalsIgnoreCase(rightString))
							return returnValue;
						else
							return !returnValue;
					case AttrOperator.aopGE:
						if(leftString.compareToIgnoreCase(rightString)>=0)
							return returnValue;
						else
							return !returnValue;
					case AttrOperator.aopGT:
						if(leftString.compareToIgnoreCase(rightString)>0)
							return returnValue;
						else
							return !returnValue;
					case AttrOperator.aopLE:
						if(leftString.compareToIgnoreCase(rightString)<=0)
							return returnValue;
						else
							return !returnValue;
					case AttrOperator.aopLT:
						if(leftString.compareToIgnoreCase(rightString)<0)
							return returnValue;
						else
							return !returnValue;
						
					case AttrOperator.aopNE:
						if(!(leftString.equalsIgnoreCase(rightString)))
							return returnValue;
						else
							return !returnValue;
						
					}
					break;
					}
				}
			}
		}
		catch(Exception e){
			//System.out.println("Exception while processing Tuple in Top Rank Join");
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
			//Added to store score as  a field
			attrCount+=inputRelations[i].length;
		}
		//System.out.println("attrCount "+attrCount);
		//count of visited relations is stored in an integer variable
		attrCount+=1;
		//System.out.println("attrCount "+attrCount);
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
				interAttr[attrIndex++] = inputRelations[i][j];

			}
			//interAttr[attrIndex++]= new AttrType(AttrType.attrReal);
		}
		interAttr[attrIndex]= new AttrType(AttrType.attrInteger);
		//create intermediate tuple header
		try {
			interTuple.setHdr((short)attrCount, interAttr, strSizes);
		} catch (InvalidTypeException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (InvalidTupleSizeException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		Heapfile interFile = null;
		try {
			interFile = new Heapfile("InterTuple.in");
		} catch (HFException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (HFBufMgrException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (HFDiskMgrException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		Heapfile tempFile = null;
		try {
			tempFile = new Heapfile("TempTuple.in");
		} catch (HFException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (HFBufMgrException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (HFDiskMgrException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
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
		}

		try {
			btf = new BTreeFile("BtreeIndex", attrType.attrType, keysize, 1);
		} catch (GetFileEntryException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (ConstructPageException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (AddFileEntryException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}	
		IndexScan interScan = null;
		try {
			for (int i = 0; i < numberOfTables; i++)
				fileScans[i] = heapFiles[i].openScan();
			while (count < knumberOfTuples) {
				for (int i = 0; i < numberOfTables; i++) {
					int tupleOffset = getTupleOffset(i);
					tuple = new Tuple();
					tuple = iterators[i].get_next();
					//System.out.println("Tuple: "+ tuple);
					
					//System.out.println("In Index scan" + tuple.getIntFld(1));
					boolean newTupleFlag=true;
					 BTreeFile btf1 = null;
					    try {
					      btf1 = new BTreeFile("BTreeIndex", attrType.attrType, 4, 1); 
					    }
					    catch (Exception e) {
					      //status = FAIL;
					      e.printStackTrace();
					      Runtime.getRuntime().exit(1);
					    }
					    Scan scan = null;
					    
					    try {
					      scan = new Scan(interFile);
				}
			    catch (Exception e) {
			      //status = FAIL;
			      e.printStackTrace();
			      Runtime.getRuntime().exit(1);
			    }
					    
					    numOfScanned[i]++;
					if(validTuple(tuple,i)){
						t= new Tuple();
						t.setHdr((short)attrCount, interAttr, strSizes);
						switch (attrType.attrType) {
						case AttrType.attrInteger:
							Tuple tt = new Tuple();
						    tt.setHdr((short)attrCount, interAttr, strSizes);
						    RID scanRid = new RID();
						    int tupleKey =0;
						    Tuple temp = null;
						    
						    try {
						      temp = scan.getNext(scanRid);
						    }
						    catch (Exception e) {
						      e.printStackTrace();
						    }
						    while ( temp != null) {
						      tt.tupleCopy(temp);
						      
						      try {
						    	  tupleKey = tt.getIntFld(joinColumns[0]+1);
						      }
						      catch (Exception e) {
							e.printStackTrace();
						      }
						      
						      try {
							btf1.insert(new IntegerKey(tupleKey), scanRid); 
						      }
						      catch (Exception e) {
							e.printStackTrace();
						      }

						      try {
							temp = scan.getNext(scanRid);
						      }
						      catch (Exception e) {
							e.printStackTrace();
						      }
						    }
						    scan.closescan();
							int key = tuple.getIntFld(joinColumns[i]+1);
							interTuple.setIntFld(joinColumns[0]+1, key);
							if(relationsVisited.size()>0){
								//System.out.println(relationsVisited.get(key));
							}
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
															expr[0].type2 = new AttrType(AttrType.attrInteger);
															expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
															expr[0].operand2.integer = key;
															expr[0].next = null;
															expr[1] = null;

															interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
															RID newRid = new RID();
															while((t = interScan.get_next())!=null){
																//get offset number of that tuple in interTuple
																int condOffset = getTupleOffset(fSpec2.relation.key);
																int offset = getTupleOffset(fSpec2.relation.key)+fSpec2.offset;
																boolean evalCondition = true;
																boolean tupleExists = true;
																switch((inputRelations[fSpec2.relation.key][offset-1]).attrType){
																case AttrType.attrInteger:
																	evalCondition = evaluateCondition(tuple.getIntFld(fSpec1.offset),t.getIntFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition && (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(key, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset, 0);
																		updateTuple(tuple,newTuple, i, tupleOffset, 1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setIntFld(joinColumns[0], key);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag = false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			relationsVisited.remove(key);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																case AttrType.attrReal:
																	evalCondition = evaluateCondition(tuple.getFloFld(fSpec1.offset),t.getFloFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(key, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setIntFld(joinColumns[0], key);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag = false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																	}else{
																		relationsVisited.remove(key);
																		interFile.deleteRecord(newRid);
																	}
																	}
																	break;
																case AttrType.attrString:
																	evalCondition = evaluateCondition(tuple.getStrFld(fSpec1.offset),t.getStrFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(key, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset, 0);
																		updateTuple(tuple,newTuple, i, tupleOffset, 1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setIntFld(joinColumns[0], key);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			relationsVisited.remove(key);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																}
															}
														}
														else{
															//write tuple to the file
															Tuple newTuple = new Tuple();
															newTuple.setHdr((short)attrCount, interAttr, strSizes);
															updateTuple(tuple,newTuple, i, tupleOffset,1);
															newTuple.setIntFld(joinColumns[0], key);
															newTuple.setIntFld(attrCount, 1);
															interFile.insertRecord(newTuple.getTupleByteArray());
															if(newTuple.getIntFld(attrCount)==numberOfTables)
																count++;
														}
													}
													else if(fSpec2.relation.key==i){
														if(relations.contains(fSpec1.relation.key)){
															CondExpr[] expr = new CondExpr[2];
															expr[0] = new CondExpr();
															expr[0].op = new AttrOperator(AttrOperator.aopEQ);
															expr[0].type1 = new AttrType(AttrType.attrSymbol);
															expr[0].type2 = new AttrType(AttrType.attrInteger);
															expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
															expr[0].operand2.integer = key;
															expr[0].next = null;
															expr[1] = null;
															
															interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
															Tuple t = new Tuple();
															t.setHdr((short)attrCount, interAttr, strSizes);
															RID newRid = new RID();
															RID prevRid = new RID();
															HashMap<String, Boolean> ridMap = new HashMap<String, Boolean>();
															
															while((t = interScan.get_next())!=null){
																//get offset number of that tuple in interTuple
																String ridKey = ""+interScan.getRID().pageNo.pid+"_"+interScan.getRID().slotNo;
																if(ridMap.containsKey(ridKey))
																	continue;
																else
																	ridMap.put(ridKey, true);
													
																if((prevRid.slotNo == interScan.getRID().slotNo) && (prevRid.pageNo.pid==interScan.getRID().pageNo.pid))
																	continue;
																int condOffset = getTupleOffset(fSpec1.relation.key);
																int offset = condOffset+fSpec1.offset;						    	
																boolean evalCondition = true;
																boolean tupleExists = false;
																switch((inputRelations[fSpec1.relation.key][offset-1]).attrType){
																case AttrType.attrInteger:
																	evalCondition = evaluateCondition(tuple.getIntFld(fSpec2.offset),t.getIntFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op );
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(key, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setIntFld(joinColumns[0], key);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			relationsVisited.remove(key);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																case AttrType.attrReal:
																	evalCondition = evaluateCondition(tuple.getFloFld(fSpec2.offset),t.getFloFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(key, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setIntFld(joinColumns[0], key);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			relationsVisited.remove(key);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																case AttrType.attrString:
																	evalCondition = evaluateCondition(tuple.getStrFld(fSpec2.offset),t.getStrFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		
																		addKeyToRelations(key, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		
																		prevRid = interFile.insertRecord(newTuple.getTupleByteArray());
																		ridMap.put(""+prevRid.pageNo.pid+"_"+prevRid.slotNo, true);
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setIntFld(joinColumns[0], key);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			relationsVisited.remove(key);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																}
															}
														}
														else{
															//write tuple to the file
															Tuple newTuple = new Tuple();
															newTuple.setHdr((short)attrCount, interAttr, strSizes);
															updateTuple(tuple,newTuple, i, tupleOffset,1);
															newTuple.setIntFld(joinColumns[0], key);
															newTuple.setIntFld(attrCount, 1);
															interFile.insertRecord(newTuple.getTupleByteArray());
															if(newTuple.getIntFld(attrCount)==numberOfTables)
																count++;
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
										//System.out.println("Size: "+ relationsVisited.get(key).size());
										int keyArraySize = relationsVisited.get(key).size();
										for (int index = 0; index < keyArraySize; index++) {
											//System.out.println("Size: "+ relationsVisited.get(key).size());
											// Add new Relation to the HashMap
											ArrayList<Integer> rel = relationsVisited.get(key).get(index);
											rel.add(i);
											relationsVisited.get(key).add(rel);											
										}
										flag = true;
										CondExpr[] condExpr = getConditionExp(i);
										boolean conditionsFlag =  true;
										if(condExpr!=null&&condExpr.length!=0){
										for(int exprIndex=0;exprIndex<condExpr.length;exprIndex++){
											CondExpr conObject = condExpr[exprIndex];
											if(conObject.operand2.symbol!=null){
												FldSpec fSpec1 = conObject.operand1.symbol;
												FldSpec fSpec2 = conObject.operand2.symbol;
												if(fSpec1.relation.key==i){
													if(relations.contains(fSpec2.relation.key)){
														CondExpr[] expr = new CondExpr[2];
														expr[0] = new CondExpr();
														expr[0].op = new AttrOperator(AttrOperator.aopEQ);
														expr[0].type1 = new AttrType(AttrType.attrSymbol);
														expr[0].type2 = new AttrType(AttrType.attrInteger);
														expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
														expr[0].operand2.integer = key;
														expr[0].next = null;
														expr[1] = null;

														interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
														Tuple t = new Tuple();
														t.setHdr((short)attrCount, interAttr, strSizes);
														RID newRid = new RID();
														while((t = interScan.get_next())!=null){
															//get offset number of that tuple in interTuple
															int condOffset = getTupleOffset(fSpec2.relation.key);
															int offset = getTupleOffset(fSpec2.relation.key)+fSpec2.offset;
															boolean evalCondition = true;
															boolean tupleExists = true;
															switch((inputRelations[fSpec2.relation.key][offset-1]).attrType){

															case AttrType.attrInteger:
																evalCondition = evaluateCondition(tuple.getIntFld(fSpec1.offset),t.getIntFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	//int arraySize = relationsVisited.get(key).size();
																	addKeyToRelations(key, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag = false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrReal:
																evalCondition = evaluateCondition(tuple.getFloFld(fSpec1.offset),t.getFloFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(key, i);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag = false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(tuple.getStrFld(fSpec1.offset),t.getStrFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(key, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															}
														}
													}
												}
												else if(fSpec2.relation.key==i){
													if(relations.contains(fSpec1.relation.key)){
														CondExpr[] expr = new CondExpr[2];
														expr[0] = new CondExpr();
														expr[0].op = new AttrOperator(AttrOperator.aopEQ);
														expr[0].type1 = new AttrType(AttrType.attrSymbol);
														expr[0].type2 = new AttrType(AttrType.attrInteger);
														expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
														expr[0].operand2.integer = key;
														expr[0].next = null;
														expr[1] = null;

														interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
														Tuple t = new Tuple();
														t.setHdr((short)attrCount, interAttr, strSizes);
														RID newRid = new RID();
														while((t = interScan.get_next())!=null){
															//get offset number of that tuple in interTuple
															newRid = interScan.getRID();
															int condOffset = getTupleOffset(fSpec1.relation.key);
															int offset = condOffset+fSpec1.offset;						    	
															boolean evalCondition = true;
															boolean tupleExists = false;
															switch((inputRelations[fSpec1.relation.key][offset-1]).attrType){

															case AttrType.attrInteger:
																evalCondition = evaluateCondition(tuple.getIntFld(fSpec2.offset),t.getIntFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op );
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag){
																	if((exprIndex+1)== condExpr.length){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(key, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																	}
																	else{
																		continue;
																	}
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0]+1, key);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrReal:
																evalCondition = evaluateCondition(tuple.getFloFld(fSpec2.offset),t.getFloFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);

																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(key, i);
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0]+1, key);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(tuple.getStrFld(fSpec2.offset),t.getStrFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
														
																	addKeyToRelations(key, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0]+1, key);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															}
														}
													}
												}
											}// no condition on relations
											else{
												CondExpr[] expr = new CondExpr[2];
												expr[0] = new CondExpr();
												expr[0].op = new AttrOperator(AttrOperator.aopEQ);
												expr[0].type1 = new AttrType(AttrType.attrSymbol);
												expr[0].type2 = new AttrType(AttrType.attrInteger);
												expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
												expr[0].operand2.integer = key;
												expr[0].next = null;
												expr[1] = null;
												interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
												RID tempRID;
												HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
												while((t = interScan.get_next())!=null){
													tempRID = interScan.getRID();
													RID currRID = interScan.getRID();
													String scanKey= ""+currRID.pageNo.pid+"_"+currRID.slotNo;
													if(randomMap.containsKey(scanKey)){
														continue;
													}
													else{
														randomMap.put(scanKey, true);
													}
													//System.out.println("RID : " + tempRID.pageNo.pid + "\t" + tempRID.slotNo);
													if(conditionsFlag){
													updateTuple(tuple, t, i, tupleOffset,1);
													t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
													interFile.updateRecord(tempRID, t);
													addKeyToRelations(key, i);
													if(t.getIntFld(attrCount)==numberOfTables)
														count++;
													}
													
												}
												
												}
										} 
										}
										else{
											CondExpr[] expr = new CondExpr[2];
											expr[0] = new CondExpr();
											expr[0].op = new AttrOperator(AttrOperator.aopEQ);
											expr[0].type1 = new AttrType(AttrType.attrSymbol);
											expr[0].type2 = new AttrType(AttrType.attrInteger);
											expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
											expr[0].operand2.integer = key;
											expr[0].next = null;
											expr[1] = null;
											interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
											RID tempRID;
											HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
											while((t = interScan.get_next())!=null){
												tempRID = interScan.getRID();
												RID currRID = interScan.getRID();
												String scanKey= ""+currRID.pageNo.pid+"_"+currRID.slotNo;
												if(randomMap.containsKey(scanKey)){
													continue;
												}
												else{
													randomMap.put(scanKey, true);
												}
												//System.out.println("RID : " + tempRID.pageNo.pid + "\t" + tempRID.slotNo);
												if(conditionsFlag){
												updateTuple(tuple, t, i, tupleOffset,1);
												t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
												interFile.updateRecord(tempRID, t);
												}
												addKeyToRelations(key, i);
												if(t.getIntFld(attrCount)==numberOfTables)
													count++;
												
												
											}
											
										}
										
									}
								}
							} else {
								// Create a new ArrayList to insert relations if
								// the key does not exists
								ArrayList<Integer> relations = new ArrayList<Integer>();
								relations.add(i);
								ArrayList<ArrayList<Integer>> tempArray = new ArrayList<ArrayList<Integer>>();
								tempArray.add(relations);
								relationsVisited.put(key, tempArray);
								Tuple newTuple = new Tuple();
								newTuple.setHdr((short)attrCount, interAttr, strSizes);
								updateTuple(tuple,newTuple, i, tupleOffset,1);
								
								newTuple.setIntFld(joinColumns[0]+1, key);
								newTuple.setIntFld(attrCount, 1);
								RID insertRid=interFile.insertRecord(newTuple.getTupleByteArray());
								if(newTuple.getIntFld(attrCount)==numberOfTables)
								count++;
							}
							break;
						case AttrType.attrReal:
							break;
						case AttrType.attrString:
							Tuple tString = new Tuple();
							tString.setHdr((short)attrCount, interAttr, strSizes);
						    RID sScanRid = new RID();
						    String sTupleKey ="";
						    Tuple temp1 = null;
						    
						    try {
						      temp1 = scan.getNext(sScanRid);
						    }
						    catch (Exception e) {
						      e.printStackTrace();
						    }
						    while ( temp1 != null) {
						    	tString.tupleCopy(temp1);
						      
						      try {
						    	  sTupleKey = tString.getStrFld(joinColumns[0]+1);
						      }
						      catch (Exception e) {
							e.printStackTrace();
						      }
						      
						      try {
							btf1.insert(new StringKey(sTupleKey), sScanRid); 
						      }
						      catch (Exception e) {
							e.printStackTrace();
						      }

						      try {
							temp1 = scan.getNext(sScanRid);
						      }
						      catch (Exception e) {
							e.printStackTrace();
						      }
						    }
						    scan.closescan();
							String sKey = tuple.getStrFld(joinColumns[i]+1);
							interTuple.setStrFld(joinColumns[0]+1, sKey);
							
							if (sRelationsVisited.containsKey(sKey)) {
								if (sRelationsVisited.get(sKey) != null) {
									ArrayList<Integer> relations = sRelationsVisited.get(sKey).get(0);
									boolean flag = false;
									for (int relationIndex = 0; relationIndex < relations.size(); relationIndex++) {
										if (i == relations.get(relationIndex)) {
											// Add relations to the hashMap
											ArrayList<Integer> newRelation = relations;
											sRelationsVisited.get(sKey).add(newRelation);
											flag = true;
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
															expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
															expr[0].operand2.string = sKey;
															expr[0].next = null;
															expr[1] = null;

															interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
															RID newRid = new RID();
															while((t = interScan.get_next())!=null){
																//get offset number of that tuple in interTuple
																int condOffset = getTupleOffset(fSpec2.relation.key);
																int offset = getTupleOffset(fSpec2.relation.key)+fSpec2.offset;
																boolean evalCondition = true;
																boolean tupleExists = true;
																switch((inputRelations[fSpec2.relation.key][offset-1]).attrType){
																case AttrType.attrInteger:
																	evalCondition = evaluateCondition(tuple.getIntFld(fSpec1.offset),t.getIntFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition && (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(sKey, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset, 0);
																		updateTuple(tuple,newTuple, i, tupleOffset, 1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setStrFld(joinColumns[0], sKey);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag = false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			sRelationsVisited.remove(sKey);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																case AttrType.attrReal:
																	evalCondition = evaluateCondition(tuple.getFloFld(fSpec1.offset),t.getFloFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(sKey, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setStrFld(joinColumns[0], sKey);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag = false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																	}else{
																		sRelationsVisited.remove(sKey);
																		interFile.deleteRecord(newRid);
																	}
																	}
																	break;
																case AttrType.attrString:
																	evalCondition = evaluateCondition(tuple.getStrFld(fSpec1.offset),t.getStrFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(sKey, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset, 0);
																		updateTuple(tuple,newTuple, i, tupleOffset, 1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setStrFld(joinColumns[0], sKey);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			relationsVisited.remove(sKey);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																}
															}
														}
														else{
															//write tuple to the file
															Tuple newTuple = new Tuple();
															newTuple.setHdr((short)attrCount, interAttr, strSizes);
															updateTuple(tuple,newTuple, i, tupleOffset,1);
															newTuple.setStrFld(joinColumns[0], sKey);
															newTuple.setIntFld(attrCount, 1);
															interFile.insertRecord(newTuple.getTupleByteArray());
															if(newTuple.getIntFld(attrCount)==numberOfTables)
																count++;
														}
													}
													else if(fSpec2.relation.key==i){
														if(relations.contains(fSpec1.relation.key)){
															CondExpr[] expr = new CondExpr[2];
															expr[0] = new CondExpr();
															expr[0].op = new AttrOperator(AttrOperator.aopEQ);
															expr[0].type1 = new AttrType(AttrType.attrSymbol);
															expr[0].type2 = new AttrType(AttrType.attrString);
															expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
															expr[0].operand2.string = sKey;
															expr[0].next = null;
															expr[1] = null;
															
															interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
															Tuple t = new Tuple();
															t.setHdr((short)attrCount, interAttr, strSizes);
															RID newRid = new RID();
															RID prevRid = new RID();
															HashMap<String, Boolean> ridMap = new HashMap<String, Boolean>();
															
															while((t = interScan.get_next())!=null){
																//get offset number of that tuple in interTuple
																String ridKey = ""+interScan.getRID().pageNo.pid+"_"+interScan.getRID().slotNo;
																if(ridMap.containsKey(ridKey))
																	continue;
																else
																	ridMap.put(ridKey, true);
													
																if((prevRid.slotNo == interScan.getRID().slotNo) && (prevRid.pageNo.pid==interScan.getRID().pageNo.pid))
																	continue;
																int condOffset = getTupleOffset(fSpec1.relation.key);
																int offset = condOffset+fSpec1.offset;						    	
																boolean evalCondition = true;
																boolean tupleExists = false;
																switch((inputRelations[fSpec1.relation.key][offset-1]).attrType){
																case AttrType.attrInteger:
																	evalCondition = evaluateCondition(tuple.getIntFld(fSpec2.offset),t.getIntFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op );
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(sKey, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setStrFld(joinColumns[0], sKey);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			sRelationsVisited.remove(sKey);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																case AttrType.attrReal:
																	evalCondition = evaluateCondition(tuple.getFloFld(fSpec2.offset),t.getFloFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		addKeyToRelations(sKey, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setStrFld(joinColumns[0], sKey);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			sRelationsVisited.remove(sKey);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																case AttrType.attrString:
																	evalCondition = evaluateCondition(tuple.getStrFld(fSpec2.offset),t.getStrFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																	tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																	//Condition evaluates to true so update the tuple
																	if(evalCondition&& (!tupleExists)){
																		updateTuple(tuple, t, i, tupleOffset,0);
																		t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																		interFile.updateRecord(newRid, t);
																		
																		addKeyToRelations(sKey, i);
																		if(t.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		
																		prevRid = interFile.insertRecord(newTuple.getTupleByteArray());
																		ridMap.put(""+prevRid.pageNo.pid+"_"+prevRid.slotNo, true);
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	else{
																		//condition fails so add the tuple as new Record in heap file
																		if(duplFlag){
																		if(newTupleFlag){
																			Tuple newTuple = new Tuple();
																			newTuple.setHdr((short)attrCount, interAttr, strSizes);
																			updateTuple(tuple,newTuple, i, tupleOffset,1);
																			newTuple.setStrFld(joinColumns[0], sKey);
																			newTuple.setIntFld(attrCount, 1);
																			interFile.insertRecord(newTuple.getTupleByteArray());
																			newTupleFlag=false;
																			if(newTuple.getIntFld(attrCount)==numberOfTables)
																				count++;
																		}
																		}else{
																			sRelationsVisited.remove(sKey);
																			interFile.deleteRecord(newRid);
																		}
																	}
																	break;
																}
															}
														}
														else{
															//write tuple to the file
															Tuple newTuple = new Tuple();
															newTuple.setHdr((short)attrCount, interAttr, strSizes);
															updateTuple(tuple,newTuple, i, tupleOffset,1);
															newTuple.setStrFld(joinColumns[0], sKey);
															newTuple.setIntFld(attrCount, 1);
															interFile.insertRecord(newTuple.getTupleByteArray());
															if(newTuple.getIntFld(attrCount)==numberOfTables)
																count++;
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
										//System.out.println("Size: "+ relationsVisited.get(key).size());
										int keyArraySize = sRelationsVisited.get(sKey).size();
										for (int index = 0; index < keyArraySize; index++) {
											//System.out.println("Size: "+ relationsVisited.get(key).size());
											// Add new Relation to the HashMap
											ArrayList<Integer> rel = sRelationsVisited.get(sKey).get(index);
											rel.add(i);
											sRelationsVisited.get(sKey).add(rel);											
										}
										flag = true;
										CondExpr[] condExpr = getConditionExp(i);
										boolean conditionsFlag =  true;
										if(condExpr!=null&&condExpr.length!=0){
										for(int exprIndex=0;exprIndex<condExpr.length;exprIndex++){
											CondExpr conObject = condExpr[exprIndex];
											if(conObject.operand2.symbol!=null){
												FldSpec fSpec1 = conObject.operand1.symbol;
												FldSpec fSpec2 = conObject.operand2.symbol;
												if(fSpec1.relation.key==i){
													if(relations.contains(fSpec2.relation.key)){
														CondExpr[] expr = new CondExpr[2];
														expr[0] = new CondExpr();
														expr[0].op = new AttrOperator(AttrOperator.aopEQ);
														expr[0].type1 = new AttrType(AttrType.attrSymbol);
														expr[0].type2 = new AttrType(AttrType.attrString);
														expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
														expr[0].operand2.string = sKey;
														expr[0].next = null;
														expr[1] = null;

														interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
														Tuple t = new Tuple();
														t.setHdr((short)attrCount, interAttr, strSizes);
														RID newRid = new RID();
														while((t = interScan.get_next())!=null){
															//get offset number of that tuple in interTuple
															int condOffset = getTupleOffset(fSpec2.relation.key);
															int offset = getTupleOffset(fSpec2.relation.key)+fSpec2.offset;
															boolean evalCondition = true;
															boolean tupleExists = true;
															switch((inputRelations[fSpec2.relation.key][offset-1]).attrType){

															case AttrType.attrInteger:
																evalCondition = evaluateCondition(tuple.getIntFld(fSpec1.offset),t.getIntFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	//int arraySize = relationsVisited.get(key).size();
																	addKeyToRelations(sKey, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setStrFld(joinColumns[0], sKey);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag = false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrReal:
																evalCondition = evaluateCondition(tuple.getFloFld(fSpec1.offset),t.getFloFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(sKey, i);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setStrFld(joinColumns[0], sKey);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag = false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(tuple.getStrFld(fSpec1.offset),t.getStrFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, sKey);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(sKey, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setStrFld(joinColumns[0], sKey);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															}
														}
													}
												}
												else if(fSpec2.relation.key==i){
													if(relations.contains(fSpec1.relation.key)){
														CondExpr[] expr = new CondExpr[2];
														expr[0] = new CondExpr();
														expr[0].op = new AttrOperator(AttrOperator.aopEQ);
														expr[0].type1 = new AttrType(AttrType.attrSymbol);
														expr[0].type2 = new AttrType(AttrType.attrString);
														expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
														expr[0].operand2.string = sKey;
														expr[0].next = null;
														expr[1] = null;

														interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
														Tuple t = new Tuple();
														t.setHdr((short)attrCount, interAttr, strSizes);
														RID newRid = new RID();
														while((t = interScan.get_next())!=null){
															//get offset number of that tuple in interTuple
															newRid = interScan.getRID();
															int condOffset = getTupleOffset(fSpec1.relation.key);
															int offset = condOffset+fSpec1.offset;						    	
															boolean evalCondition = true;
															boolean tupleExists = false;
															switch((inputRelations[fSpec1.relation.key][offset-1]).attrType){

															case AttrType.attrInteger:
																evalCondition = evaluateCondition(tuple.getIntFld(fSpec2.offset),t.getIntFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op );
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag){
																	if((exprIndex+1)== condExpr.length){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(sKey, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																	}
																	else{
																		continue;
																	}
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setStrFld(joinColumns[0]+1, sKey);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrReal:
																evalCondition = evaluateCondition(tuple.getFloFld(fSpec2.offset),t.getFloFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);

																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
																	addKeyToRelations(sKey, i);
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setStrFld(joinColumns[0]+1, sKey);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(tuple.getStrFld(fSpec2.offset),t.getStrFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(!evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&& ((exprIndex+1)== condExpr.length)){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
																	interFile.updateRecord(newRid, t);
														
																	addKeyToRelations(sKey, i);
																	if(t.getIntFld(attrCount)==numberOfTables)
																		count++;
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setStrFld(joinColumns[0]+1, sKey);
																		newTuple.setIntFld(attrCount, 1);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																		if(newTuple.getIntFld(attrCount)==numberOfTables)
																			count++;
																	}
																	}
																}
																break;
															}
														}
													}
												}
											}// no condition on relations
											else{
												CondExpr[] expr = new CondExpr[2];
												expr[0] = new CondExpr();
												expr[0].op = new AttrOperator(AttrOperator.aopEQ);
												expr[0].type1 = new AttrType(AttrType.attrSymbol);
												expr[0].type2 = new AttrType(AttrType.attrString);
												expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
												expr[0].operand2.string = sKey;
												expr[0].next = null;
												expr[1] = null;
												interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
												RID tempRID;
												HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
												while((t = interScan.get_next())!=null){
													tempRID = interScan.getRID();
													RID currRID = interScan.getRID();
													String scanKey= ""+currRID.pageNo.pid+"_"+currRID.slotNo;
													if(randomMap.containsKey(scanKey)){
														continue;
													}
													else{
														randomMap.put(scanKey, true);
													}
													//System.out.println("RID : " + tempRID.pageNo.pid + "\t" + tempRID.slotNo);
													if(conditionsFlag){
													updateTuple(tuple, t, i, tupleOffset,1);
													System.out
															.println(" AttrCount: "+ t.getIntFld(attrCount));
													t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
													interFile.updateRecord(tempRID, t);
													addKeyToRelations(sKey, i);
													if(t.getIntFld(attrCount)==numberOfTables)
														count++;
													}
													
												}
												
												}
										} 
										}
										else{
											CondExpr[] expr = new CondExpr[2];
											expr[0] = new CondExpr();
											expr[0].op = new AttrOperator(AttrOperator.aopEQ);
											expr[0].type1 = new AttrType(AttrType.attrSymbol);
											expr[0].type2 = new AttrType(AttrType.attrString);
											expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
											expr[0].operand2.string = sKey;
											expr[0].next = null;
											expr[1] = null;
											interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
											RID tempRID;
											HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
											while((t = interScan.get_next())!=null){
												tempRID = interScan.getRID();
												RID currRID = interScan.getRID();
												String scanKey= ""+currRID.pageNo.pid+"_"+currRID.slotNo;
												if(randomMap.containsKey(scanKey)){
													continue;
												}
												else{
													randomMap.put(scanKey, true);
												}
												//System.out.println("RID : " + tempRID.pageNo.pid + "\t" + tempRID.slotNo);
												if(conditionsFlag){
												updateTuple(tuple, t, i, tupleOffset,1);
												//t.print(t.attr_Types);
												System.out.println("count count: "+ t.getIntFld(attrCount));
												t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
												t.print(t.attr_Types);
												interFile.updateRecord(tempRID, t);
												}
												addKeyToRelations(sKey, i);
												if(t.getIntFld(attrCount)==numberOfTables){
													count++;
												tempFile.insertRecord(t.getTupleByteArray());	
												}
												
											}
											
										}
										
									}
								}
							} else {
								// Create a new ArrayList to insert relations if
								// the key does not exists
								ArrayList<Integer> relations = new ArrayList<Integer>();
								relations.add(i);
								ArrayList<ArrayList<Integer>> tempArray = new ArrayList<ArrayList<Integer>>();
								tempArray.add(relations);
								sRelationsVisited.put(sKey, tempArray);
								Tuple newTuple = new Tuple();
								newTuple.setHdr((short)attrCount, interAttr, strSizes);
								updateTuple(tuple,newTuple, i, tupleOffset,1);
								
								newTuple.setStrFld(joinColumns[0]+1, sKey);
								newTuple.setIntFld(attrCount, 1);
								RID insertRid=interFile.insertRecord(newTuple.getTupleByteArray());
								if(newTuple.getIntFld(attrCount)==numberOfTables)
								count++;
							}
							break;
							
						}// end of switch
					}//end of if
					//System.out.println("count: "+ count);
					if(count>=knumberOfTuples&&i+1==numberOfTables)break;
				}//end of for
			}//end of while
			Heapfile resultsFile = null;
			Tuple finalTuple = new Tuple();
			switch (attrType.attrType) {
			case AttrType.attrInteger:
			IndexScan iscan[] = new IndexScan[numberOfTables];
			Set<Integer> keySet = relationsVisited.keySet();
			//Create heap file to store final results
			
			try {
				resultsFile = new Heapfile("ResultTuple.in");
			} catch (HFException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (HFBufMgrException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (HFDiskMgrException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			//Tuple finalTuple = new Tuple();
			
			for(java.util.Iterator<Integer> it = keySet.iterator(); it.hasNext(); ){
				int visitKey = it.next();

				CondExpr[] expr = new CondExpr[2];
				expr[0] = new CondExpr();
				expr[0].op = new AttrOperator(AttrOperator.aopEQ);
				expr[0].type1 = new AttrType(AttrType.attrSymbol);
				expr[0].type2 = new AttrType(AttrType.attrInteger);
				
				expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
				expr[0].operand2.integer = visitKey;
				expr[0].next = null;
				expr[1] = null;

				interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
				Tuple mainTuple = new Tuple();
				mainTuple.setHdr((short)attrCount, interAttr, strSizes);
				RID newRid = new RID();
				//System.out.println("attrCount "+attrCount);
				
				//Get all tuples obtained in the sorted phase
				RID prevRID = new RID();
				HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
				while((mainTuple = interScan.get_next())!=null){
					//System.out.println("i "+i);
					/*RID currRID = interScan.getRID();
					String scanKey= ""+currRID.pageNo.pid+"_"+currRID.slotNo;
					if(randomMap.containsKey(scanKey)){
						continue;
					}
					else{
						randomMap.put(scanKey, true);
					}
					
					

					if(currRID.pageNo.pid==prevRID.pageNo.pid && currRID.slotNo==prevRID.slotNo)
						continue;
					
					prevRID.pageNo.pid = currRID.pageNo.pid;
					prevRID.slotNo = currRID.slotNo;*/
					System.out.println("Inside random tuple loop");
					mainTuple.print(interAttr);
					if(mainTuple.getIntFld(attrCount)!=numberOfTables){
						
						for(int relNumber=0;relNumber<numberOfTables;relNumber++){
							int condOffset = getTupleOffset(relNumber);
							boolean tupleExists = doesTupleExists(mainTuple, condOffset+1, true, attrType, visitKey);
							if(!tupleExists){
								//Do random access and get the data onto the tuple
								CondExpr[] randomExpr = new CondExpr[2];
								randomExpr[0] = new CondExpr();
								randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
								randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
								randomExpr[0].type2 = new AttrType(AttrType.attrInteger);
								randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[relNumber]+1);
								randomExpr[0].operand2.integer = visitKey;
								randomExpr[0].next = null;
								randomExpr[1] = null;

								int attrLength = inputRelations[relNumber].length;
								//create projectionList for Index Scan
								FldSpec [] Sprojection = new FldSpec[attrLength];
								for(int attr=0; attr<attrLength; attr++){
									Sprojection[attr]= new FldSpec(new RelSpec(RelSpec.outer), attr+1);
								}
								//Index Scan
								
								IndexScan testScan = null;
								testScan = new IndexScan(new IndexType(IndexType.B_Index), fileNames[relNumber], indexFileNames[relNumber], inputRelations[relNumber], stringSizes[relNumber], inputRelations[relNumber].length, inputRelations[relNumber].length, Sprojection, randomExpr, joinColumns[relNumber]+1, false);
								Tuple randomTuple = new Tuple();
								randomTuple.setHdr((short)inputRelations[relNumber].length, inputRelations[relNumber], stringSizes[relNumber]);
								//For all tuples in the relations missing
								//Check if new tuple should be created
								while((randomTuple=testScan.get_next())!=null){
									//Copy tuple contents into the tuple and write to index file
									//Write into tuple and completely writeTuple
									numOfProbed[relNumber]++;
									if(validTuple(randomTuple, relNumber)){
										
									int tupleOffset = getTupleOffset(relNumber);
									CondExpr[] condExpr = getConditionExp(relNumber);
									boolean conditionsFlag =  true;
									if(condExpr.length!=0){
									for(int exprIndex=0;exprIndex<condExpr.length;exprIndex++){
										CondExpr conObject = condExpr[exprIndex];
										if(conObject.operand2.symbol!=null){
											FldSpec fSpec1 = conObject.operand1.symbol;
											FldSpec fSpec2 = conObject.operand2.symbol;
											if(fSpec1.relation.key==relNumber){
												int keyOffset = getTupleOffset(fSpec2.relation.key);
												int conditionalOffset = keyOffset+fSpec2.offset;
												if(randomTuple.getIntFld(keyOffset)==visitKey){
														boolean evalCondition = true;
														switch((inputRelations[fSpec1.relation.key][fSpec1.offset]).attrType){
														case AttrType.attrInteger:
															evalCondition = evaluateCondition(randomTuple.getIntFld(fSpec1.offset),mainTuple.getIntFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
															if(evalCondition)
																conditionsFlag = false;
															if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
															}
															break;
														case AttrType.attrReal:
															evalCondition = evaluateCondition(randomTuple.getFloFld(fSpec1.offset),mainTuple.getFloFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition)
																conditionsFlag = false;
															if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
															}
															break;
														case AttrType.attrString:
															evalCondition = evaluateCondition(randomTuple.getStrFld(fSpec1.offset),mainTuple.getStrFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition)
																conditionsFlag = false;
															if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
															}
															break;
														}
													}
												}
											else if(fSpec2.relation.key==relNumber){
												
												int keyOffset = getTupleOffset(fSpec1.relation.key);
												int conditionalOffset = keyOffset+fSpec1.offset;
												
														if(randomTuple.getIntFld(keyOffset+1)==visitKey){
													boolean evalCondition = true;
														switch((inputRelations[fSpec2.relation.key][fSpec2.offset-1]).attrType){
														case AttrType.attrInteger:
															evalCondition = evaluateCondition(randomTuple.getIntFld(fSpec2.offset),mainTuple.getIntFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset]),conObject.op );
															//Condition evaluates to true so update the tuple
															if(evalCondition)
																conditionsFlag = false;
															if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
															}
														case AttrType.attrReal:
															evalCondition = evaluateCondition(randomTuple.getFloFld(fSpec2.offset),mainTuple.getFloFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition)
																conditionsFlag = false;
															if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
																//interFile.updateRecord(newRid, t);
															}
															break;
														case AttrType.attrString:
															evalCondition = evaluateCondition(randomTuple.getStrFld(fSpec2.offset),mainTuple.getStrFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset-1]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition)
																conditionsFlag = false;
															if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
															}
															break;
														} //end of Switch
													} //end of visitKey check
												} //end of fSpec2 if
											} //operand check
										} //end of condition Expression for loop
									}
									else{
										updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
										System.out.println("get Field Count: "+ mainTuple.getIntFld(attrCount) );
										mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
									}
									}
									} //random Scan while
								} //tupleExists if
							} //relations check for loop
						} //total relations in a tuple check
					/** TO BE MODIFIED -- Update Count**/
					
					if(mainTuple.getIntFld(attrCount)==numberOfTables){
					Tuple outTuple = new Tuple();
					AttrType[] Restypes = new AttrType[numOutputFlds];
					
					short[] t_size= TupleUtils.setup_op_tuple(outTuple, Restypes, inputRelations, lengths,
							stringSizes, proj_list, numOutputFlds);
					int attrSizes = outTuple.attrSizes;
					AttrType[] outAttrTypes = outTuple.attr_Types;
					AttrType[] attrArray = new AttrType[attrSizes+1];
					for(int attrIndex1=0;attrIndex1<attrSizes;attrIndex1++){
						attrArray[attrIndex1] = outAttrTypes[attrIndex1];
						
					}
					attrArray[attrSizes] = new AttrType(AttrType.attrReal);
					//set final Tuple header
					finalTuple.setHdr((short) (outTuple.noOfFlds() + 1), attrArray,outTuple.string_sizes);
					
					for(int projIndex=0;projIndex<numOutputFlds;projIndex++){
						FldSpec fldSpec = proj_list[projIndex];
						//System.out.println("flllddspec: "+fldSpec);
						int projOffset = getTupleOffset(proj_list[projIndex].relation.key)+ fldSpec.offset;	
						
						switch(interAttr[projOffset-1].attrType){
						case AttrType.attrInteger:
							finalTuple.setIntFld(projIndex+1, mainTuple.getIntFld(projOffset));
							
							break;
						case AttrType.attrReal:
							finalTuple.setFloFld(projIndex+1, mainTuple.getFloFld(projOffset));
							
							break;
						case AttrType.attrString:
							
							finalTuple.setStrFld(projIndex+1, mainTuple.getStrFld(projOffset));
							
							break;
						}
					}
					float score = 0.0f;
					for(int scoreIndex=0;scoreIndex<numberOfTables;scoreIndex++){
						score+= mainTuple.getFloFld(inputRelations[scoreIndex].length+getTupleOffset(scoreIndex));
					}
					finalTuple.setFloFld(proj_list.length+1, score/numberOfTables);
					fileRid = outFile.insertRecord(finalTuple.getTupleByteArray());
					/** TO BE MODIFIED - Check the count and throw error if does not exist **/
					//Now do projection and write results to a new heap file
					}
				}
				
				
			}	
			get_topK("TopRankJoin.in", finalTuple);
			interScan.close();
			break;
			case AttrType.attrString:
				IndexScan siscan[] = new IndexScan[numberOfTables];
				Set<String> sKeySet = sRelationsVisited.keySet();
				//Create heap file to store final results
				//Heapfile resultsFile = null;
				try {
					resultsFile = new Heapfile("ResultTuple.in");
				} catch (HFException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				} catch (HFBufMgrException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				} catch (HFDiskMgrException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				} catch (IOException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
				
				
				for(java.util.Iterator<String> it = sKeySet.iterator(); it.hasNext(); ){
					String visitKey = it.next();

					CondExpr[] expr = new CondExpr[2];
					expr[0] = new CondExpr();
					expr[0].op = new AttrOperator(AttrOperator.aopEQ);
					expr[0].type1 = new AttrType(AttrType.attrSymbol);
					expr[0].type2 = new AttrType(AttrType.attrString);
					
					expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
					expr[0].operand2.string = visitKey;
					expr[0].next = null;
					expr[1] = null;

					interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0]+1, false);
					Tuple mainTuple = new Tuple();
					Tuple newTuple = new Tuple();
					boolean randomFlag = false;
					mainTuple.setHdr((short)attrCount, interAttr, strSizes);
					RID newRid = new RID();
					//System.out.println("attrCount "+attrCount);
					
					//Get all tuples obtained in the sorted phase
					RID prevRID = new RID();
					HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
					while((mainTuple = interScan.get_next())!=null){
						//System.out.println("i "+i);
						RID currRID = interScan.getRID();
						String scanKey= ""+currRID.pageNo.pid+"_"+currRID.slotNo;
						if(randomMap.containsKey(scanKey)){
							continue;
						}
						else{
							randomMap.put(scanKey, true);
						}

						if(currRID.pageNo.pid==prevRID.pageNo.pid && currRID.slotNo==prevRID.slotNo)
							continue;
						
						//System.out.println("Main Tuple :" + mainTuple.getStrFld(1) + " Count: " + mainTuple.getIntFld(attrCount));
						
						prevRID.pageNo.pid = currRID.pageNo.pid;
						prevRID.slotNo = currRID.slotNo;
						if(mainTuple.getIntFld(attrCount)!=numberOfTables){
							for(int relNumber=0;relNumber<numberOfTables;relNumber++){
								int condOffset = getTupleOffset(relNumber);
								boolean tupleExists = doesTupleExists(mainTuple, condOffset+1, true, attrType, visitKey);
								if(!tupleExists){
									//Do random access and get the data onto the tuple
									CondExpr[] randomExpr = new CondExpr[2];
									randomExpr[0] = new CondExpr();
									randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
									randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
									randomExpr[0].type2 = new AttrType(AttrType.attrString);
									randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[relNumber]+1);
									randomExpr[0].operand2.string = visitKey;
									randomExpr[0].next = null;
									randomExpr[1] = null;

									int attrLength = inputRelations[relNumber].length;
									//create projectionList for Index Scan
									FldSpec [] Sprojection = new FldSpec[attrLength];
									for(int attr=0; attr<attrLength; attr++){
										Sprojection[attr]= new FldSpec(new RelSpec(RelSpec.outer), attr+1);
									}
									IndexScan testScan = null;
									testScan = new IndexScan(new IndexType(IndexType.B_Index), fileNames[relNumber], indexFileNames[relNumber], inputRelations[relNumber], stringSizes[relNumber], inputRelations[relNumber].length, inputRelations[relNumber].length, Sprojection, randomExpr, joinColumns[relNumber]+1, false);
									Tuple randomTuple = new Tuple();
									
									randomTuple.setHdr((short)inputRelations[relNumber].length, inputRelations[relNumber], stringSizes[relNumber]);
									//For all tuples in the relations missing
									//Check if new tuple should be created
									RID prevRID1 = new RID();
									HashMap<String, Boolean> randomMap1 = new HashMap<String, Boolean>();
									while((randomTuple=testScan.get_next())!=null){
										//Copy tuple contents into the tuple and write to index file
										//Write into tuple and completely writeTuple
										String randomTupleKeyString = randomTuple.getStrFld(1);
										//System.out.println("Random Tuple" + randomTupleKeyString + " Score : " + randomTuple.getScore());
										RID currRID1 = testScan.getRID();
										/*String scanKey1= ""+currRID1.pageNo.pid+"_"+currRID1.slotNo;
										if(randomMap1.containsKey(scanKey)){
											continue;
										}
										else{
											randomMap1.put(scanKey, true);
										}*/
										numOfProbed[relNumber]++;
										
										
										
										if(validTuple(randomTuple, relNumber)){
											
										int tupleOffset = getTupleOffset(relNumber);
										CondExpr[] condExpr = getConditionExp(relNumber);
										boolean conditionsFlag =  true;
										if(condExpr.length!=0){
										for(int exprIndex=0;exprIndex<condExpr.length;exprIndex++){
											CondExpr conObject = condExpr[exprIndex];
											if(conObject.operand2.symbol!=null){
												FldSpec fSpec1 = conObject.operand1.symbol;
												FldSpec fSpec2 = conObject.operand2.symbol;
												if(fSpec1.relation.key==relNumber){
													int keyOffset = getTupleOffset(fSpec2.relation.key);
													int conditionalOffset = keyOffset+fSpec2.offset;
													if(randomTuple.getStrFld(keyOffset)==visitKey){
															boolean evalCondition = true;
															switch((inputRelations[fSpec1.relation.key][fSpec1.offset]).attrType){
															case AttrType.attrInteger:
																evalCondition = evaluateCondition(randomTuple.getIntFld(fSpec1.offset),mainTuple.getIntFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
																if(evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																	updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																	mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
																}
																break;
															case AttrType.attrReal:
																evalCondition = evaluateCondition(randomTuple.getFloFld(fSpec1.offset),mainTuple.getFloFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
																//Condition evaluates to true so update the tuple
																if(evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																	updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																	mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(randomTuple.getStrFld(fSpec1.offset),mainTuple.getStrFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
																//Condition evaluates to true so update the tuple
																if(evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																	updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																	mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
																}
																break;
															}
														}
													}
												else if(fSpec2.relation.key==relNumber){
													
													int keyOffset = getTupleOffset(fSpec1.relation.key);
													int conditionalOffset = keyOffset+fSpec1.offset;
													
															if(randomTuple.getStrFld(keyOffset+1)==visitKey){
														boolean evalCondition = true;
															switch((inputRelations[fSpec2.relation.key][fSpec2.offset-1]).attrType){
															case AttrType.attrInteger:
																evalCondition = evaluateCondition(randomTuple.getIntFld(fSpec2.offset),mainTuple.getIntFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset]),conObject.op );
																//Condition evaluates to true so update the tuple
																if(evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																	updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																	mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
																}
															case AttrType.attrReal:
																evalCondition = evaluateCondition(randomTuple.getFloFld(fSpec2.offset),mainTuple.getFloFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset]),conObject.op);
																//Condition evaluates to true so update the tuple
																if(evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																	updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																	mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
																	//interFile.updateRecord(newRid, t);
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(randomTuple.getStrFld(fSpec2.offset),mainTuple.getStrFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset-1]),conObject.op);
																//Condition evaluates to true so update the tuple
																if(evalCondition)
																	conditionsFlag = false;
																if(conditionsFlag&&(exprIndex+1)==condExpr.length){
																	updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																	mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
																}
																break;
															} //end of Switch
														} //end of visitKey check
													} //end of fSpec2 if
												} //operand check
											} //end of condition Expression for loop
										}
										else{
											
											if(mainTuple.getIntFld(attrCount)==numberOfTables){
										
												newTuple.setHdr((short)attrCount, interAttr, strSizes);
												newTuple.tupleCopy(mainTuple);
												updateTuple(randomTuple,newTuple,relNumber, tupleOffset, 1);
												newTuple.print(interAttr);
												RID insertRID = tempFile.insertRecord(newTuple.getTupleByteArray());
												System.out.println("Inserted record in " + insertRID.slotNo + ";" + insertRID.pageNo);
												System.out.println("In First If");
												Tuple tempTupleFile = tempFile.getRecord(insertRID);
												tempTupleFile.setHdr((short)attrCount, interAttr, strSizes);
												tempTupleFile.print(interAttr);
												randomFlag = true;
											}
											if(mainTuple.getIntFld(attrCount)!=numberOfTables){
												System.out.println("In Second If");
												updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
												int keyOffset = getTupleOffset(relNumber);
												System.out.println("Key Offset : " + keyOffset);
												boolean tupleCheck = doesTupleExists(mainTuple, keyOffset+1, true, inputRelations[relNumber][joinColumns[relNumber]], visitKey);
												System.out.println("Tuple check value: " + tupleCheck);
												if(!tupleCheck)
													mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount)+1);
												mainTuple.print(interAttr);
											
											}
										}
										}
										} //random Scan while
									} //tupleExists if
								} //relations check for loop
							} //total relations in a tuple check
						/** TO BE MODIFIED -- Update Count**/
						
						
					}
					
					
				}	
				//FileScan finalResults = new FileScan("InterTuple.in",interAttr,strSizes,(short)interAttr.length,numOutputFlds,proj_list,null);
				interScan.close();
				
				//IndexScan finalScan = new IndexScan(new IndexType(IndexType.B_Index), "TempTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, null, joinColumns[0]+1, false);
				
				Scan finalResults = new Scan(tempFile);
				Tuple mainTuple = new Tuple();
				RID newRID = new RID();
				System.out.println("Before going into loop");
				while((mainTuple=finalResults.getNext(newRID))!=null){
					//System.out.println("Near Table count check");
					System.out.println("RID values: " + newRID.slotNo + ";" + newRID.pageNo);
					//System.out.println(mainTuple.getStrFld(1) + " Count: " + mainTuple.getIntFld(attrCount));
					//System.out.println("Final Tuple : " + mainTuple.getStrFld(1));
					System.out.println("In loop before check");
					mainTuple.setHdr((short)attrCount, interAttr, strSizes);
					mainTuple.print(interAttr);

					if(mainTuple.getIntFld(attrCount)==numberOfTables){
						System.out.println("In loop after check");
						mainTuple.print(interAttr);
						//System.out.println("Inside final check : " + mainTuple.getStrFld(1));
						Tuple outTuple = new Tuple();
						AttrType[] Restypes = new AttrType[numOutputFlds];

						short[] t_size= TupleUtils.setup_op_tuple(outTuple, Restypes, inputRelations, lengths,
								stringSizes, proj_list, numOutputFlds);
						int attrSizes = outTuple.attrSizes;
						AttrType[] outAttrTypes = outTuple.attr_Types;
						AttrType[] attrArray = new AttrType[attrSizes+1];
						for(int attrIndex1=0;attrIndex1<attrSizes;attrIndex1++){
							attrArray[attrIndex1] = outAttrTypes[attrIndex1];

						}
						attrArray[attrSizes] = new AttrType(AttrType.attrReal);
						//set final Tuple header
						finalTuple.setHdr((short) (outTuple.noOfFlds() + 1), attrArray,outTuple.string_sizes);

						for(int projIndex=0;projIndex<numOutputFlds;projIndex++){
							FldSpec fldSpec = proj_list[projIndex];
							//System.out.println("flllddspec: "+fldSpec);
							int projOffset = getTupleOffset(proj_list[projIndex].relation.key)+ fldSpec.offset;	

							switch(interAttr[projOffset-1].attrType){
							case AttrType.attrInteger:
								finalTuple.setIntFld(projIndex+1, mainTuple.getIntFld(projOffset));

								break;
							case AttrType.attrReal:
								finalTuple.setFloFld(projIndex+1, mainTuple.getFloFld(projOffset));

								break;
							case AttrType.attrString:

								finalTuple.setStrFld(projIndex+1, mainTuple.getStrFld(projOffset));

								break;
							}
						}
						float score = 0.0f;
						for(int scoreIndex=0;scoreIndex<numberOfTables;scoreIndex++){
							//System.out.println(mainTuple.getFloFld(inputRelations[scoreIndex].length+getTupleOffset(scoreIndex)));
							score+= mainTuple.getFloFld(inputRelations[scoreIndex].length+getTupleOffset(scoreIndex));
						}
						finalTuple.setFloFld(proj_list.length+1, score/numberOfTables);
						//System.out.println("Final Tuple value : " + finalTuple.getStrFld(1)); 
						fileRid = outFile.insertRecord(finalTuple.getTupleByteArray());
						/** TO BE MODIFIED - Check the count and throw error if does not exist **/
						//Now do projection and write results to a new heap file

					}
				}
				get_topK("TopRankJoin.in", finalTuple);
				interScan.close();
			
		}// end of try
			
		}
		catch (Exception e) {
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

		TupleOrder order = new TupleOrder(TupleOrder.Descending);
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
					//System.out.println("tuple1: "+tuple1.getStrFld(1));
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
			if(tableCondition!=null && tableCondition.operand1.symbol!=null){
				if(tableCondition.operand1.symbol.relation.key==tableIndex){
				condExp.add(tableCondition);
			}
				else if (tableCondition!=null && tableCondition.operand2.symbol!=null){
					if(tableCondition.operand2.symbol.relation.key==tableIndex){
						condExp.add(tableCondition);
					}
				}
			}
		}	
		CondExpr[] cExpr = new CondExpr[condExp.size()];
		 for(int i=0;i<condExp.size();i++){
			 cExpr[i] = condExp.get(i);
		 }
		 
		return cExpr;
	}

	private int getTupleOffset(int tableIndex){
		int offset = 0;
		if(tableIndex==0){
			return 0;
		}
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

	private void updateTuple(Tuple inTuple,Tuple outTuple, int tableIndex, int offset, int newTuple){
		int fieldCount =1;
		Tuple Jtuple = new Tuple();
		/*if(offset==0){
			offset++;
		}*/
		int attrLength = inputRelations[tableIndex].length;
		//System.out.println("offset: "+ offset);
		for(int tField=1;tField<=attrLength;tField++){
			switch(inputRelations[tableIndex][tField-1].attrType){
			case AttrType.attrInteger:
				try {
					outTuple.setIntFld(offset+1,
							inTuple.getIntFld(fieldCount));
					//System.out.println("integer: "+inTuple.getIntFld(fieldCount));
					fieldCount++;
					offset++;
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
					//System.out.println("float: " +inTuple.getFloFld(fieldCount));
					fieldCount++;
					offset++;
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
					//System.out.println("String: "+ inTuple.getStrFld(fieldCount));
					fieldCount++;
					offset++;
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
		int keyArraySize = relationsVisited.get(key).size();
		for (int index = 0; index < keyArraySize; index++) {
			// Add new Relation to the HashMap
			ArrayList<Integer> rel = relationsVisited.get(key).get(index);
			rel.add(tableIndex);
			relationsVisited.get(key).add(rel);											
		}
	}
	
	private void addKeyToRelations(String key, int tableIndex){
		int keyArraySize = sRelationsVisited.get(key).size();
		for (int index = 0; index < keyArraySize; index++) {
			// Add new Relation to the HashMap
			ArrayList<Integer> rel = sRelationsVisited.get(key).get(index);
			rel.add(tableIndex);
			sRelationsVisited.get(key).add(rel);											
		}
	}

	private boolean doesTupleExists(Tuple t, int keyOffset, boolean tupleExists, AttrType keyAttr, Object key){
		if(keyOffset==1){
			int counter = 0;
			try{
				for(int i=0;i<inputRelations[0].length;i++){
					switch(inputRelations[0][i].attrType){
					case AttrType.attrInteger:
						if(t.getIntFld(i+1)!=0){
							System.out.println("field: "+ t.getIntFld(i+1));
							counter++;
						}
						break;
					case AttrType.attrReal:
						if(t.getFloFld(i+1)!=0.0){
							System.out.println("field: "+ t.getFloFld(i+1));
							counter++;
						}
						break;
					case AttrType.attrString:
						if(!(t.getStrFld(i+1).equals(""))){
							System.out.println("field: "+ t.getStrFld(i+1));
							counter++;
						}
						break;
					}
				}
				System.out.println("Counter: "+counter);
				if(counter==1)
					return false;
				else
					return true;
			}
			catch(Exception e){
				System.out.println("Exception caught at doesTupleExists");
			}
		}
		else{
			switch(keyAttr.attrType){
			case AttrType.attrInteger:
				try {
					if((Integer)key==t.getIntFld(keyOffset)){
						return true;
					}
					return false;
				} catch (FieldNumberOutOfBoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			case AttrType.attrReal:
				try {
					if((Float)key==t.getFloFld(keyOffset)){
						return true;
					}
					return false;
				} catch (FieldNumberOutOfBoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			case AttrType.attrString:
				try {
					System.out.println("String field error comes now");
					AttrType[] attr = t.attr_Types;
					for(int i=0;i<attr.length;i++){
						System.out.println(i +": "+attr[i]);
					}
					System.out.println("Key Offset: "+ keyOffset);
					System.out.println(t.getStrFld(keyOffset));
					if(key.toString().equals(t.getStrFld(keyOffset))){
						return true;
					}
					return false;
				} catch (FieldNumberOutOfBoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		return false;
	}
}