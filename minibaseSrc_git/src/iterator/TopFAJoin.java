package iterator;

import global.AttrOperator;
import global.AttrType;
import global.ConstantVars;
import global.GlobalConst;
import global.IndexType;
import global.RID;
import global.TupleOrder;
import heap.FieldNumberOutOfBoundException;
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
import index.UnknownIndexTypeException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;

import javax.swing.GroupLayout.SequentialGroup;

import btree.AddFileEntryException;
import btree.BTreeFile;
import btree.ConstructPageException;
import btree.GetFileEntryException;
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
	private RID fileRid;
	private boolean firstTime;
	private String[] indexFileNames;
	private boolean duplFlag= false;
	private String[] fileNames;
	private Tuple combinedTuple = new Tuple();
	private Tuple t = new Tuple();
	private RID newRid = new RID();
	private int combinedAttrCount = 0;
	private Heapfile tempFile = null;
	private FileScan fScan = null;
	private Tuple mainTuple = new Tuple();
	private AttrType[] combinedAttr =null;
	private short[] combinedStrSizes = null;
	private FldSpec [] combinedProjection = null;

	public TopFAJoin(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			IndexType[] index, java.lang.String[] indNames, int amt_of_mem,
			CondExpr[] outFilter, FldSpec[] proj_list, int n_out_flds, int num,
			int rank, String[] fileNames) throws IOException, TopRankJoinException {
		
		//System.out.println("in TopFA");
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
		for(int i=0;i<inputRelations.length;i++){
			combinedAttrCount+=inputRelations[i].length;
		}
		for(int i=0;i<stringSizes.length;i++){
				strAttrCount+=stringSizes[i].length;
		}
		if(inputRelations[0][joinColumns[0]].attrType== AttrType.attrString){
			strAttrCount+=1;
		}
		combinedAttrCount+=2;
		int attrCount =0;
		int strCount=0;
		combinedAttr = new AttrType[combinedAttrCount];
		combinedStrSizes = new short[strAttrCount];
		for(int i =0;i<inputRelations.length;i++){
			int count=0;
			for(int j=0;j<inputRelations[i].length;j++){
				//System.out.println("attr length: "+ inputRelations[i].length);
				combinedAttr[attrCount++] = inputRelations[i][j];
				if(inputRelations[i][j].attrType==AttrType.attrString)
					combinedStrSizes[strCount++] = stringSizes[i][count++];
			}
		}
		combinedAttr[attrCount++] = new AttrType(AttrType.attrInteger);
		if(inputRelations[0][joinColumns[0]].attrType== AttrType.attrInteger){
			combinedAttr[attrCount++] = new AttrType(AttrType.attrInteger);
		}
		else if(inputRelations[0][joinColumns[0]].attrType== AttrType.attrString){
			combinedAttr[attrCount++] = new AttrType(AttrType.attrString);
			combinedStrSizes[strCount++] = 20;
		}
		combinedProjection = new FldSpec[combinedAttrCount];
		for(int attr=0; attr<combinedAttrCount; attr++){
			combinedProjection[attr]= new FldSpec(new RelSpec(RelSpec.outer), attr+1);
		}
		for(int i=0;i<combinedAttr.length;i++){
			//System.out.println("i: "+combinedAttr[i]);
		}
		try {
			combinedTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
			mainTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
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

	public void createTopKTuples() {
		int count =0;
		Tuple fileTuple = new Tuple();
		RID ridScan = new RID();
		Tuple scanTuple = new Tuple();
		AttrType keyAttrType = new AttrType(inputRelations[0][joinColumns[0]].attrType);
		//System.out.println("in create topK");
		while(count<knumberOfTuples){
			for(int relNum=0;relNum<numberOfTables;relNum++){
				try {
					//fileTuple.setHdr((short)inputRelations[relNum].length, inputRelations[relNum], stringSizes[relNum]);
					fileTuple =  iterators[relNum].get_next();
					//fileTuple.print(inputRelations[relNum]);
					if(fileTuple==null)
						continue;
					String strKey ="";
					ridScan = ConstantVars.getGlobalRID();
					String rid = Integer.toString(ridScan.pageNo.pid)+"_"+Integer.toString(ridScan.slotNo);
					 BTreeFile btf1 = null;
					 scanTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
					 int keySize = 4;
					    try {
					    	switch(inputRelations[relNum][joinColumns[relNum]].attrType){
					    	case AttrType.attrInteger:
					    		strKey = String.valueOf(fileTuple.getIntFld(joinColumns[relNum]+1));
					    		keySize = 4;
					    		break;
					    	case AttrType.attrString:
					    		strKey = fileTuple.getStrFld(joinColumns[relNum]+1);
					    		keySize = 20;
					    		break;
					    	}
					      btf1 = new BTreeFile("BTreeIndex", inputRelations[relNum][joinColumns[relNum]].attrType, keySize, 1); 
					    }
					    catch (Exception e) {
					      e.printStackTrace();
					      Runtime.getRuntime().exit(1);
					    }
					Scan scan = null;
				    RID sScanRid = new RID();
				    String sTupleKey ="";
				    int tupleKey=0;
				    Tuple temp1 = null;
				    try {
				      scan = new Scan(tempFile);
				      temp1 = scan.getNext(sScanRid);
				    }
				    catch (Exception e) {
				      e.printStackTrace();
				    }
				    while ( temp1 != null) {
				    	scanTuple.tupleCopy(temp1);
				      try {
				    	  switch(inputRelations[relNum][joinColumns[relNum]].attrType){
							case AttrType.attrInteger:
								tupleKey = scanTuple.getIntFld(combinedAttrCount);
						    	btf1.insert(new IntegerKey(tupleKey), sScanRid);
						    	break;
							case AttrType.attrString:
								sTupleKey = scanTuple.getStrFld(combinedAttrCount);
						    	btf1.insert(new StringKey(sTupleKey), sScanRid);
						    	break;
						}
				    	  temp1 = scan.getNext(sScanRid);
				      }
				      catch (Exception e) {
				    	  e.printStackTrace();
				      }
				    }
				    count+= sequentialAccess(fileTuple, keyAttrType, strKey, relNum, rid);
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
		randomAcess();
		//fScan.close();
		try {
			fScan = new FileScan("TempResults.in", combinedAttr , combinedStrSizes, (short)combinedAttrCount, combinedAttrCount, combinedProjection, null);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple testTuple = new Tuple();
		try {
			while((testTuple=fScan.get_next())!=null){
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
				rScan = new FileScan("TempResults.in", combinedAttr , combinedStrSizes, (short)combinedAttrCount, combinedAttrCount, combinedProjection, null);
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} 
		AttrType keyAttrType = inputRelations[0][joinColumns[0]];
		try {
			while((mainTuple=rScan.get_next())!=null){
				RID ridScan = ConstantVars.getGlobalRID();
				RID mainRID = new RID();
				mainRID.pageNo = ridScan.pageNo;
				mainRID.slotNo = ridScan.slotNo;
				String strKey = "";
				if(inputRelations[0][joinColumns[0]].attrType==AttrType.attrInteger){
					strKey = String.valueOf(mainTuple.getIntFld(combinedAttrCount));
				}
				else{
					strKey = mainTuple.getStrFld(combinedAttrCount);
				}
				String rid = Integer.toString(ridScan.pageNo.pid)+"-"+Integer.toString(ridScan.slotNo);	
				if(mainTuple.getIntFld(combinedAttrCount-1)!=numberOfTables){
					for(int i=0;i<numberOfTables;i++){
						if(relationExists(i, strKey, mainTuple)){
							continue;
						}
						else{
							CondExpr[] randomExpr = new CondExpr[2];
							randomExpr[0] = new CondExpr();
							randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
							randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
							randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[i]+1);
							if(keyAttrType.attrType==AttrType.attrInteger){
								randomExpr[0].type2 = new AttrType(AttrType.attrInteger);
								randomExpr[0].operand2.integer = mainTuple.getIntFld(combinedAttrCount);
							}
							else if(keyAttrType.attrType==AttrType.attrString){
								randomExpr[0].type2 = new AttrType(AttrType.attrString);
								randomExpr[0].operand2.string = mainTuple.getStrFld(combinedAttrCount);
							}
							randomExpr[0].next = null;
							randomExpr[1] = null;
							FldSpec[] fSpec = new FldSpec[inputRelations[i].length];
							for(int j=0;j<inputRelations[i].length;j++){
								fSpec[j] = new FldSpec(new RelSpec(RelSpec.outer), j+1);
							}
							IndexScan iScan = new IndexScan(new IndexType(IndexType.B_Index), fileNames[i], indexFileNames[i], inputRelations[i], stringSizes[i], inputRelations[i].length, inputRelations[i].length, fSpec, randomExpr, joinColumns[i]+1, false);
							Tuple indexTuple = new Tuple();
							Heapfile interFile = new Heapfile("interFile.in");
							RID prevRID = new RID();
							HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
							while((indexTuple=iScan.get_next())!=null){
								RID currRID = iScan.getRID();
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
								prevRID.slotNo = currRID.slotNo;
								interFile.insertRecord(indexTuple.getTupleByteArray());
							}
							if(interFile.getRecCnt()>0){
							FileScan fm1 = null;
							try {
								fm1 = new FileScan("interFile.in", inputRelations[i], stringSizes[i],
										(short)inputRelations[i].length, inputRelations[i].length,
										fSpec, null);
							} catch (Exception e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
							TupleOrder order = new TupleOrder(TupleOrder.Descending);
							Iterator topIterator = new Sort(inputRelations[i],(short)inputRelations[i].length,
										stringSizes[i], fm1, inputRelations[i].length, order, 4, 10);
							Tuple newTuple = topIterator.get_next();
							topIterator.close();
							fm1.close();
							interFile.deleteFile();
							//mainTuple.print(combinedAttr);
							updateTuple(newTuple, mainTuple, i, getTupleOffset(i), rid);
							mainTuple.setIntFld(combinedAttrCount-1, mainTuple.getIntFld(combinedAttrCount-1)+1);
							mainTuple.setStrFld(combinedAttrCount, strKey);
							//mainTuple.print(combinedAttr);
							//System.out.println("ridScan: "+mainRID.pageNo.pid+"_"+mainRID.slotNo);
							tempFile.updateRecord(mainRID, mainTuple);
							}
						}
					}
				}
				mainTuple=null;
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
		
	}

	private int sequentialAccess(Tuple fileTuple, AttrType keyAttrType, String strKey, int relNum, String rid) {
		combinedTuple = new Tuple();
		try {
			combinedTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} 
		int count=0;
		CondExpr[] randomExpr = new CondExpr[2];
		randomExpr[0] = new CondExpr();
		randomExpr[0].op = new AttrOperator(AttrOperator.aopEQ);
		randomExpr[0].type1 = new AttrType(AttrType.attrSymbol);
		randomExpr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[relNum]+1);
		if(keyAttrType.attrType==AttrType.attrInteger){
			randomExpr[0].type2 = new AttrType(AttrType.attrInteger);
			randomExpr[0].operand2.integer = Integer.parseInt(strKey);
		}
		else if(keyAttrType.attrType==AttrType.attrString){
			randomExpr[0].type2 = new AttrType(AttrType.attrString);
			randomExpr[0].operand2.string = strKey;
		}
		randomExpr[0].next = null;
		randomExpr[1] = null;
	    IndexScan tempScan=null;
	    RID prevRID = new RID();
		try {
			tempScan = new IndexScan(new IndexType(IndexType.B_Index), "TempResults.in", "BTreeIndex", combinedAttr, combinedStrSizes, combinedAttrCount, combinedAttrCount, combinedProjection, randomExpr, combinedAttrCount, false);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
		boolean keyExists = false;
	    try {
	    	HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
			while((t=tempScan.get_next())!=null){
				RID currRID = tempScan.getRID();
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
				prevRID.slotNo = currRID.slotNo;
				keyExists = true;
				combinedTuple.tupleCopy(t);
				if(relationExists(relNum, strKey, combinedTuple)){
					updateTuple(fileTuple, combinedTuple, relNum, getTupleOffset(relNum), rid);
					RID rs = tempFile.insertRecord(combinedTuple.getTupleByteArray());
				}
				else{
					RID updateRid = ConstantVars.getGlobalRID();
					updateTuple(fileTuple, combinedTuple, relNum, getTupleOffset(relNum), rid);
					combinedTuple.setIntFld(combinedAttrCount-1, combinedTuple.getIntFld(combinedAttrCount-1)+1);
					tempFile.updateRecord(updateRid, combinedTuple);
				}
				if(combinedTuple.getIntFld(combinedAttrCount-1)==numberOfTables){
					//combinedTuple.print(combinedAttr);
					count++;
				}
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
		if(!keyExists){
			updateTuple(fileTuple, combinedTuple, relNum, getTupleOffset(relNum), rid);
			try {
				combinedTuple.setIntFld(combinedAttrCount-1, combinedTuple.getIntFld(combinedAttrCount-1)+1);
				if(keyAttrType.attrType==AttrType.attrInteger){
					combinedTuple.setIntFld(combinedAttrCount, Integer.parseInt(strKey));
				}
				else if(keyAttrType.attrType==AttrType.attrString){
					combinedTuple.setStrFld(combinedAttrCount, strKey);
				}
				tempFile.insertRecord(combinedTuple.getTupleByteArray());
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} 
			
		}
		// TODO Auto-generated method stub
		return count;
	}

	public boolean relationExists(int relNum, String strKey, Tuple jTuple){
		int keyOffset = getTupleOffset(relNum);
		if(inputRelations[0][joinColumns[0]].attrType==AttrType.attrInteger){
			try {
				if(jTuple.getIntFld(keyOffset)==Integer.parseInt(strKey))
					return true;
			} catch (FieldNumberOutOfBoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		else if(inputRelations[0][joinColumns[0]].attrType==AttrType.attrString){
			try {
				if((jTuple.getStrFld(keyOffset).equals(strKey)))
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
					tuple1.print(outTuple.attr_Types);
				}
				topK--;
			}  catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}


	private int getTupleOffset(int tableIndex){
		int offset = 0;
		if(tableIndex==0){
			return 1;
		}
		for(int i=0;i<tableIndex;i++){
			offset+=inputRelations[i].length;
		}
		return offset+1;

	}

	private void updateTuple(Tuple inTuple,Tuple outTuple, int tableIndex, int offset, String rid){
		int fieldCount =1;
		Tuple Jtuple = new Tuple();
		int attrLength = inputRelations[tableIndex].length;
		for(int tField=1;tField<=attrLength;tField++){
			switch(inputRelations[tableIndex][tField-1].attrType){
			case AttrType.attrInteger:
				try {
					outTuple.setIntFld(offset,
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
					outTuple.setFloFld(offset, inTuple.getFloFld(fieldCount));
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
					outTuple.setStrFld(offset, inTuple.getStrFld(fieldCount));
					fieldCount++;
					offset++;
				} catch (FieldNumberOutOfBoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (IOException e) {
					e.printStackTrace();
				}
				break;
			}
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
							counter++;
						}
						break;
					case AttrType.attrReal:
						if(t.getFloFld(i+1)!=0.0){
							counter++;
						}
						break;
					case AttrType.attrString:
						if(!(t.getStrFld(i+1).equals(""))){
							counter++;
						}
						break;
					}
				}
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
					AttrType[] attr = t.attr_Types;
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