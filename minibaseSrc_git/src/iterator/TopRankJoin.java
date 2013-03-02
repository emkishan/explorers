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
	private boolean duplFlag= true;
	private HashMap<Integer, ArrayList<ArrayList<RIDScore>>> ridScore = new HashMap<Integer, ArrayList<ArrayList<RIDScore>>>();
	private HashMap<Integer, ArrayList<ArrayList<Integer>>> relationsVisited = new HashMap<Integer, ArrayList<ArrayList<Integer>>>();

	public TopRankJoin(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			IndexType[] index, java.lang.String[] indNames, int amt_of_mem,
			CondExpr[] outFilter, FldSpec[] proj_list, int n_out_flds, int num,
			int rank) throws IOException, TopRankJoinException {

		numberOfTables = numTables;
		inputRelations = new AttrType[numTables][];
		indexFileNames = indNames;
		outFile = null;
		try {
			outFile = new Heapfile("Test.in");
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
			//Added to store score as  a field
			attrCount+=inputRelations[i].length+1;
		}
		//count of visited relations is stored in an integer variable
		attrCount+=inputRelations.length+1;
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
			interAttr[attrIndex++]= new AttrType(AttrType.attrReal);
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
					tuple = fileScans[i].getNext(rid);
					boolean newTupleFlag=true;
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
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset, 0);
																		updateTuple(tuple,newTuple, i, tupleOffset, 1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
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
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
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
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec2.relation.key, condOffset, 0);
																		updateTuple(tuple,newTuple, i, tupleOffset, 1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
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
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
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
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
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
																	}
																	else if(evalCondition&&tupleExists&&duplFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(t, newTuple,fSpec1.relation.key, condOffset,0);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(attrCount, 2);
																		interFile.insertRecord(newTuple.getTupleByteArray());
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
															int condOffset = getTupleOffset(fSpec2.relation.key);
															int offset = getTupleOffset(fSpec2.relation.key)+fSpec2.offset;
															boolean evalCondition = true;
															boolean tupleExists = true;
															switch((inputRelations[fSpec2.relation.key][offset-1]).attrType){

															case AttrType.attrInteger:
																evalCondition = evaluateCondition(tuple.getIntFld(fSpec1.offset),t.getIntFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(evalCondition){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	interFile.updateRecord(newRid, t);
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag = false;
																	}
																	}
																}
																break;
															case AttrType.attrReal:
																evalCondition = evaluateCondition(tuple.getFloFld(fSpec1.offset),t.getFloFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(evalCondition){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	interFile.updateRecord(newRid, t);
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag = false;
																	}
																	}
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(tuple.getStrFld(fSpec1.offset),t.getStrFld(offset),(inputRelations[fSpec2.relation.key][offset-1]),conObject.op);
																tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(evalCondition){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	interFile.updateRecord(newRid, t);
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
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
															int condOffset = getTupleOffset(fSpec1.relation.key);
															int offset = condOffset+fSpec1.offset;						    	
															boolean evalCondition = true;
															boolean tupleExists = false;
															switch((inputRelations[fSpec1.relation.key][offset-1]).attrType){

															case AttrType.attrInteger:
																evalCondition = evaluateCondition(tuple.getIntFld(fSpec2.offset),t.getIntFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op );
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(evalCondition){
																	updateTuple(tuple, t, i, tupleOffset,1);
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
																		newTuple.setIntFld(joinColumns[0], key);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																	}
																	}
																}
																break;
															case AttrType.attrReal:
																evalCondition = evaluateCondition(tuple.getFloFld(fSpec2.offset),t.getFloFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);

																//Condition evaluates to true so update the tuple
																if(evalCondition){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	interFile.updateRecord(newRid, t);
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																	}
																	}
																}
																break;
															case AttrType.attrString:
																evalCondition = evaluateCondition(tuple.getStrFld(fSpec2.offset),t.getStrFld(offset),(inputRelations[fSpec1.relation.key][offset-1]),conObject.op);
																//tupleExists = doesTupleExists(t, condOffset+1, tupleExists, attrType, key);
																//Condition evaluates to true so update the tuple
																if(evalCondition){
																	updateTuple(tuple, t, i, tupleOffset,1);
																	interFile.updateRecord(newRid, t);
																}
																else{
																	//condition fails so add the tuple as new Record in heap file
																	if(duplFlag){
																	if(newTupleFlag){
																		Tuple newTuple = new Tuple();
																		newTuple.setHdr((short)attrCount, interAttr, strSizes);
																		updateTuple(tuple,newTuple, i, tupleOffset,1);
																		newTuple.setIntFld(joinColumns[0], key);
																		interFile.insertRecord(newTuple.getTupleByteArray());
																		newTupleFlag=false;
																	}
																	}
																}
																break;
															}
														}
													}
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
								ArrayList<ArrayList<Integer>> temp = new ArrayList<ArrayList<Integer>>();
								temp.add(relations);
								relationsVisited.put(key, temp);
								Tuple newTuple = new Tuple();
								newTuple.setHdr((short)attrCount, interAttr, strSizes);
								updateTuple(tuple,newTuple, i, tupleOffset,1);
								newTuple.setIntFld(joinColumns[0], key);
								interFile.insertRecord(newTuple.getTupleByteArray());
							}
							count++;
							break;
						case AttrType.attrReal:
							/*HashMap<Float, ArrayList<ArrayList<RIDScore>>> ridScoreF = new HashMap<Float, ArrayList<ArrayList<RIDScore>>>();
						HashMap<Float, ArrayList<ArrayList<Integer>>> relationsVisitedF = new HashMap<Float, ArrayList<ArrayList<Integer>>>();*/
							break;
						case AttrType.attrString:

							break;
						}// end of switch
					}//end of if
				}//end of for
			}//end of while
			IndexScan iscan[] = new IndexScan[numberOfTables];
			Set<Integer> keySet = relationsVisited.keySet();
			//Create heap file to store final results
			Heapfile resultsFile = null;
			try {
				interFile = new Heapfile("ResultTuple.in");
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
			for(java.util.Iterator<Integer> it = keySet.iterator(); it.hasNext(); ){
				Integer visitKey = it.next();

				CondExpr[] expr = new CondExpr[1];
				expr[0] = new CondExpr();
				expr[0].op = new AttrOperator(AttrOperator.aopEQ);
				expr[0].type1 = new AttrType(AttrType.attrSymbol);
				expr[0].type2 = new AttrType(AttrType.attrString);
				expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]);
				expr[0].operand2.integer = visitKey;
				expr[0].next = null;
				expr[1] = null;

				interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, joinColumns[0], false);
				Tuple mainTuple = new Tuple();
				mainTuple.setHdr((short)attrCount, interAttr, strSizes);
				RID newRid = new RID();
				Tuple finalTuple = new Tuple();
				//Get all tuples obtained in the sorted phase
				while((mainTuple = interScan.get_next(newRid))!=null){
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
								randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[relNumber]);
								randomExpr[0].operand2.integer = visitKey;
								randomExpr[0].next = null;
								expr[1] = null;

								int attrLength = inputRelations[relNumber].length;
								//create projectionList for Index Scan
								FldSpec [] Sprojection = new FldSpec[attrLength];
								for(int attr=0; attr<attrLength; attr++){
									Sprojection[attr]= new FldSpec(new RelSpec(RelSpec.outer), attr+1);
								}
								//Index Scan
								IndexScan randomScan = new IndexScan(new IndexType(IndexType.B_Index), indexFileNames[relNumber], "BTreeIndex", inputRelations[relNumber], stringSizes[relNumber], attrLength, attrLength, Sprojection, randomExpr, joinColumns[relNumber], false);
								Tuple randomTuple = new Tuple();
								randomTuple.setHdr((short)(inputRelations[relNumber].length), inputRelations[relNumber], stringSizes[relNumber]);
								//For all tuples in the relations missing
								//Check if new tuple should be created
								while((randomTuple=randomScan.get_next())!=null){
									//Copy tuple contents into the tuple and write to index file
									//Write into tuple and completely writeTuple
									int tupleOffset = getTupleOffset(relNumber);
									CondExpr[] condExpr = getConditionExp(relNumber);
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
															if(evalCondition){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount));
															}
															break;
														case AttrType.attrReal:
															evalCondition = evaluateCondition(randomTuple.getFloFld(fSpec1.offset),mainTuple.getFloFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount));
															}
															break;
														case AttrType.attrString:
															evalCondition = evaluateCondition(randomTuple.getStrFld(fSpec1.offset),mainTuple.getStrFld(conditionalOffset),(inputRelations[fSpec1.relation.key][fSpec1.offset-1]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount));
															}
															break;
														}
													}
												}
											else if(fSpec2.relation.key==relNumber){
												int keyOffset = getTupleOffset(fSpec1.relation.key);
												int conditionalOffset = keyOffset+fSpec1.offset;
												if(randomTuple.getIntFld(keyOffset)==visitKey){
													boolean evalCondition = true;
														switch((inputRelations[fSpec2.relation.key][fSpec2.offset]).attrType){
														case AttrType.attrInteger:
															evalCondition = evaluateCondition(randomTuple.getIntFld(fSpec2.offset),mainTuple.getIntFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset]),conObject.op );
															//Condition evaluates to true so update the tuple
															if(evalCondition){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount));
															}
														case AttrType.attrReal:
															evalCondition = evaluateCondition(randomTuple.getFloFld(fSpec2.offset),mainTuple.getFloFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount));
																//interFile.updateRecord(newRid, t);
															}
															break;
														case AttrType.attrString:
															evalCondition = evaluateCondition(randomTuple.getStrFld(fSpec2.offset),mainTuple.getStrFld(conditionalOffset),(inputRelations[fSpec2.relation.key][fSpec2.offset]),conObject.op);
															//Condition evaluates to true so update the tuple
															if(evalCondition){
																updateTuple(randomTuple, mainTuple, relNumber, tupleOffset, 1);
																mainTuple.setIntFld(attrCount, mainTuple.getIntFld(attrCount));
															}
															break;
														} //end of Switch
													} //end of visitKey check
												} //end of fSpec2 if
											} //operand check
										} //end of condition Expression for loop
									} //random Scan while
								} //tupleExists if
							} //relations check for loop
						} //total relations in a tuple check
					/** TO BE MODIFIED -- Update Count**/
					Tuple outTuple = new Tuple();
					AttrType[] Restypes = new AttrType[numOutputFlds];
					short[] t_size= TupleUtils.setup_op_tuple(outTuple, Restypes, inputRelations, lengths,
							stringSizes, proj_list, numOutputFlds);
					int attrSizes = outTuple.attrSizes;
					AttrType[] outAttrTypes = outTuple.attr_Types;
					AttrType[] attrArray = new AttrType[attrSizes+1];
					for(int attrIndex1=0;attrIndex1<attrArray.length;attrIndex1++){
						attrArray[attrIndex1] = outAttrTypes[attrIndex1];
					}
					attrArray[attrSizes] = new AttrType(AttrType.attrReal);
					//set final Tuple header
					finalTuple.setHdr((short) (outTuple.noOfFlds() + 1), attrArray,outTuple.string_sizes);
					for(int projIndex=0;projIndex<proj_list.length;projIndex++){
						FldSpec fldSpec = proj_list[projIndex];
						int projOffset = getTupleOffset(proj_list[projIndex].relation.key)+ fldSpec.offset;	
						switch(attrArray[projOffset].attrType){
						case AttrType.attrInteger:
							finalTuple.setIntFld(projIndex+1, mainTuple.getIntFld(projIndex));
							break;
						case AttrType.attrReal:
							finalTuple.setFloFld(projIndex+1, mainTuple.getFloFld(projIndex));
							break;
						case AttrType.attrString:
							finalTuple.setStrFld(projIndex+1, mainTuple.getStrFld(projIndex));
							break;
						}
					}
					float score = 0.0f;
					for(int scoreIndex=0;scoreIndex<numberOfTables;scoreIndex++){
						score+= mainTuple.getFloFld(inputRelations[scoreIndex].length+1);
					}
					finalTuple.setFloFld(proj_list.length+1, score/numberOfTables);
					fileRid = outFile.insertRecord(finalTuple.getTupleByteArray());
					/** TO BE MODIFIED - Check the count and throw error if does not exist **/
					//Now do projection and write results to a new heap file
				}
				get_topK("TopRankJoin.in", finalTuple);
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
		if(tableIndex==0){
			return 0;
		}
		for(int i=0;i<tableIndex;i++){
			offset+=inputRelations[i].length+1;
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
		int attrLength = inputRelations[tableIndex].length+1;
		if(newTuple==1){
			attrLength = inputRelations[tableIndex].length;
		}
		for(int tField=1;tField<=attrLength;tField++){
			switch(inputRelations[tableIndex][tField].attrType){
			case AttrType.attrInteger:
				try {
					outTuple.setIntFld(offset + 1,
							inTuple.getIntFld(fieldCount));
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
		if(newTuple==1){
			try {
				outTuple.setFloFld(offset, inTuple.getScore());
			} catch (FieldNumberOutOfBoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
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

	private boolean doesTupleExists(Tuple t, int keyOffset, boolean tupleExists, AttrType keyAttr, Object key){

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
				if(key.toString()==t.getStrFld(keyOffset)){
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
		return false;
	}
}