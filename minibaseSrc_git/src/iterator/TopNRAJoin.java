package iterator;

import index.IndexException;
import index.IndexScan;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;


import btree.BTreeFile;
import btree.IntegerKey;
import btree.RealKey;
import btree.StringKey;
import bufmgr.HashEntryNotFoundException;
import bufmgr.InvalidFrameNumberException;
import bufmgr.PageNotReadException;
import bufmgr.PageUnpinnedException;
import bufmgr.ReplacerException;

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
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Scan;
import heap.Tuple;

public class TopNRAJoin {

	private int numberOfTables;
	private AttrType inputRelations[][];
	private int lengths[];
	private short[][] stringSizes;
	private int joinColumns[];
	private Iterator iterators[];
	private int n_buf_pgs;
	private CondExpr[] outFilter;
	private FldSpec[] proj_list;
	private int numOutputFlds;
	private int topK;
	private Heapfile heapFiles[], outFile,dupCheckIndexFile,interFile;
	//creating duplicate heap file with header key as intger only. going forward put key as string as well
	private float threshold;
	private float minTopK;
	private float bestScore;
	private float worstScore;
	private int numOfScanned[];
	private Tuple t = new Tuple();
	private float scorePerRelation[];
	AttrType[] interAttr;
	short[] strSizes;
	int attrCount=0;
	FldSpec [] tProjection;
	String [] tableNameList;
	String [] indexNameList;
	String [] fileNames;
	IndexType[] b_index;
	BTreeFile btf = null;
	BTreeFile dupBtf = null;
	AttrType[] dupInterAttr = null;
	Tuple interTuple = null;
	FldSpec[] dupTProjection = null;
	
	public TopNRAJoin(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			int amt_of_mem, CondExpr[] outFilter, FldSpec[] proj_list, 
			int n_out_flds, int num, String[] tableNameList,String [] indexNameList) throws IOException, TopRankJoinException {
		
		numberOfTables = numTables;
		inputRelations = in;		
		lengths = len_in;
		stringSizes = s_sizes;
		joinColumns = join_col_in;
		iterators = am;
		n_buf_pgs = amt_of_mem;
		outFile = null;
		dupCheckIndexFile = null;
		this.outFilter = outFilter;
		this.proj_list = proj_list;
		numOutputFlds = n_out_flds;
		topK = num;
		//topK = num + 20;
		numOfScanned = new int[numTables];
		this.tableNameList = tableNameList; 
		
		//Create Btree Index File on Relation
		b_index = new IndexType[numberOfTables];
		this.indexNameList = indexNameList;
		fileNames = new String[numberOfTables];
		for(int k=0;k<numberOfTables;k++){
			fileNames[k] = tableNameList[k]+".in";
			//indexNameList[k] = tableNameList[k]+"_BTreeIndex";
		}
		//constructBtreeIndexFileOnRelation();
	
		try {
			//we ll keep candidates hers in outfile
			outFile = new Heapfile("TopNRAJoin.in");
			dupCheckIndexFile = new Heapfile("DupCheckTopNRAJoin.in");
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
		/*System.out.println("numberOfTables = "+numberOfTables);
		for(int i=0;i<inputRelations.length;i++)
			for(int j=0;j<inputRelations[i].length;j++)
			System.out.println("AttrType = "+inputRelations[i][j].attrType);
		for(int i=0;i<lengths.length;i++)
			System.out.println("lengths = "+lengths[i]);
		for(int i=0;i<stringSizes.length;i++)
			System.out.println("stringSizes = "+stringSizes[i][0]);
		for(int i=0;i<join_col_in.length;i++)
			System.out.println("join_col_in = "+join_col_in[i]);
		
		for(int j=0;j<numberOfTables;j++){
			
			Iterator ed=iterators[j];
			
			Tuple t2 = null;
			try {
			      while ((t2 = ed.get_next()) != null) {
			        t2.print(inputRelations[j]);
			        //System.out.println("t2.getScore()"+t2.getScore());
			        //qcheck4.Check(t2);
			      }
			    }
			    catch (Exception e) {
			      System.err.println (""+e);
			      e.printStackTrace(); 
			      Runtime.getRuntime().exit(1);
			      }
		
		}
		
		System.out.println("n_buf_pages = "+n_buf_pgs);
		System.out.println("numOutputFlds = "+numOutputFlds);
		System.out.println("topK = "+topK);*/
		createTopKTuples();
		System.out.println("end of create top k tuples.");
//		getTopK();
		System.out.println("end of get top k");
		//for(int i=0; i<numOfScanned.length ; i++)
		for(int i : numOfScanned)
			System.out.println("numOfScanned = "+i);		
	}
	
		public void AddTopNRAJoin(ArrayList itrList,ArrayList relationList,ArrayList<String> relationNames) throws IOException{
		Tuple tuple;
		IndexScan dupInterScan = null;
		IndexScan interScan = null;
		for(int i=0;i<itrList.size();i++){
			Iterator am = (Iterator)itrList.get(i);
			int relation = (int)relationList.get(i);
		try {
			int tupleOffset= getTupleOffset(relation);
			AttrType attrType = new AttrType(inputRelations[0][joinColumns[0]].attrType);
			while((tuple =am.get_next())!=null){
				//tuple.print(inputRelations[relation]);
				Scan scan = null;
			    Scan dupScan = null;
				try {
					btf = new BTreeFile("BTreeIndex", attrType.attrType,strSizes[0], 1);
					dupBtf = new BTreeFile("DupBTreeIndex",attrType.attrType, strSizes[0], 1);
					scan = new Scan(interFile);
					dupScan = new Scan(dupCheckIndexFile);
				} catch (Exception e) {
					// status = FAIL;
					e.printStackTrace();
					Runtime.getRuntime().exit(1);
				}
				//numOfScanned[i]++;
				t= new Tuple();
				t.setHdr((short)attrCount, interAttr, strSizes);
				
				switch (attrType.attrType) {
				
				case AttrType.attrString:
				Tuple tt = new Tuple();
			    tt.setHdr((short)attrCount, interAttr, strSizes);
			    Tuple duptt = new Tuple();
			    duptt.setHdr((short)(numberOfTables+1), dupInterAttr, strSizes);
			    RID scanRid = new RID();
			    RID dupScanRid = new RID();
			    String tupleKey =null;
			    String dupTupleKey =null;
			    Tuple temp = null;
			    Tuple dupTemp = null;
			    
			    
			    try {
			      temp = scan.getNext(scanRid);
			      dupTemp = dupScan.getNext(dupScanRid);
			    }
			    catch (Exception e) {
			      e.printStackTrace();
			    }
			    
			    while ( temp != null) {
				      tt.tupleCopy(temp);
				      
				      try {
				    	  tupleKey = tt.getStrFld(attrCount);
				    	  //btree index is created
						  btf.insert(new StringKey(tupleKey), scanRid);
						  temp = scan.getNext(scanRid);
				      }
				      catch (Exception e) {
				    	  e.printStackTrace();
				      }
				    }
				    scan.closescan();
				    btf.close();
				    while ( dupTemp != null) {
					      duptt.tupleCopy(dupTemp);
					      
					      try {
					    	  dupTupleKey = duptt.getStrFld(joinColumns[0]+1);
					    	  //btree index is created
					    	  dupBtf.insert(new StringKey(dupTupleKey), dupScanRid);
					    	  dupTemp = dupScan.getNext(dupScanRid);
					      }
					      catch (Exception e) {
					    	  e.printStackTrace();
					      }	      
					    					     
					    }
					 dupScan.closescan();   
					 dupBtf.close();
				    
					 	//create btree file, then a scan for it, open scan read join column, put this as key in index 
					    String key = tuple.getStrFld(joinColumns[relation]+1);
						interTuple.setStrFld(joinColumns[0]+1, key);
						boolean too = true;
						Tuple dup2 = new Tuple();
						dup2.setHdr((short)(numberOfTables+1), dupInterAttr, strSizes);
						CondExpr[] expr = new CondExpr[2];
						expr[0] = new CondExpr();
						expr[0].op = new AttrOperator(AttrOperator.aopEQ);
						expr[0].type1 = new AttrType(AttrType.attrSymbol);
						expr[0].type2 = new AttrType(AttrType.attrString);
						expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), attrCount);
						expr[0].operand2.string = key;
						expr[0].next = null;
						expr[1] = null;
						
						CondExpr[] expr1 = new CondExpr[2];
						expr1[0] = new CondExpr();
						expr1[0].op = new AttrOperator(AttrOperator.aopEQ);
						expr1[0].type1 = new AttrType(AttrType.attrSymbol);
						expr1[0].type2 = new AttrType(AttrType.attrString);
						expr1[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[relation]+1);
						expr1[0].operand2.string = key;
						expr1[0].next = null;
						expr1[1] = null;
						
						//expr=null;
						dupInterScan = new IndexScan(new IndexType(IndexType.B_Index), "DupCheckTopNRAJoin.in", "DupBTreeIndex", dupInterAttr, strSizes, (numberOfTables+1), (numberOfTables+1), dupTProjection, expr1, 1, false);
						interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, attrCount, false);
						
						/*Tuple t1;
						System.out.println("**************Internscan******************");
						while((t1 =interScan.get_next())!=null){							
							t1.print(interAttr);
						}	
						System.out.println("**************DupInternscan******************");
						while((t1 =dupInterScan.get_next())!=null){							
							t1.print(dupInterAttr);
						}*/
							
						RID dupTempRID;
						HashMap<String, Boolean> dupRandomMap = new HashMap<String, Boolean>();
						RID tempRID;
						HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
						
						
						bestScore=0;
						worstScore=0;
						dup2 = dupInterScan.get_next();
						if ((dup2) != null) {
							dupTempRID = dupInterScan.getRID();
							RID currRID = dupInterScan.getRID();
							
							String scanKey = "" + currRID.pageNo.pid + "_"+ currRID.slotNo;
							if (dupRandomMap.containsKey(scanKey)) {
								continue;
							} else {
								dupRandomMap.put(scanKey, true);
							}
							int isSet = dup2.getIntFld((relation + 2));
							if (isSet == 1) {
								if((t = interScan.get_next())!=null){
									Tuple newTuple = new Tuple();
									newTuple.setHdr((short)attrCount, interAttr, strSizes);
									newTuple.tupleCopy(t);
									/*System.out.println("$$$$After$$$$$$$$");
									newTuple.print(interAttr);*/
									updateTuple(tuple, newTuple, relation, tupleOffset,1);
									for(int j=0;j<numberOfTables;j++){
										if(newTuple.getStrFld(joinColumns[j]+getTupleOffset(j)+1)!=null){
											bestScore += newTuple.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
											worstScore += newTuple.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
										}
										else{
											bestScore += scorePerRelation[j];
										}
									}
									newTuple.setFloFld(attrCount-1, worstScore);
									newTuple.setFloFld(attrCount-2, bestScore);
									//newTuple.print(interAttr);
									if(minTopK<bestScore){
									RID insertRid1=interFile.insertRecord(newTuple.getTupleByteArray());
									}
									printTuples();
								}
							}else {
								dup2.setIntFld((relation + 2), 1);
								dupCheckIndexFile.updateRecord(dupTempRID, dup2);
								while((t = interScan.get_next())!=null){
									tempRID = interScan.getRID();
									RID currRID1 = interScan.getRID();
									String scanKey1= ""+currRID1.pageNo.pid+"_"+currRID1.slotNo;
									if(randomMap.containsKey(scanKey1)){
										continue;
									}
									else{
										randomMap.put(scanKey1, true);
									}
									updateTuple(tuple, t, relation, tupleOffset,1);
									bestScore=0.0f;
									worstScore=0.0f;
									for(int j=0;j<numberOfTables;j++){
										if(t.getStrFld(getTupleOffset(j)+joinColumns[j]+1)!=null){
											bestScore += t.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
											worstScore += t.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
										}
										else{
											bestScore += scorePerRelation[j];
										}
									}
									t.setFloFld(attrCount-1, worstScore);
									t.setFloFld(attrCount-2, bestScore);
									//System.out.println("update after updating");
									//t.print(interAttr);
									if(minTopK<bestScore){
										interFile.updateRecord(tempRID, t);
									}
																
								}
							}
							dupInterScan.close();
							interScan.close();
							}	
						else{
							//System.out.println("@@@@@@ This tuple is new @@@@@");
							//tuple.print(inputRelations[relation]);
							if(relation==0){
								for(int j=1;j<itrList.size();j++){
									//Iterator am1 = (Iterator)itrList.get(j);
									//Condition for scanning the original relation
									int attrCount1 = inputRelations[j].length-1;
									FldSpec[] tProjection = new FldSpec[attrCount1];
									for (int k = 0; k < attrCount1; k++)
										tProjection[k] = new FldSpec(new RelSpec(RelSpec.outer), k + 1);
									CondExpr[] expr2 = new CondExpr[2];
									expr2[0] = new CondExpr();
									expr2[0].op = new AttrOperator(AttrOperator.aopEQ);
									expr2[0].type1 = new AttrType(AttrType.attrSymbol);
									expr2[0].type2 = new AttrType(AttrType.attrString);
									expr2[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
									expr2[0].operand2.string = key;
									expr2[0].next = null;
									expr2[1] = null;
									
									//expr2=null;
									
									//see if scan is created correctly
									int attrIndex = 0;
					    			AttrType[] tempAttr = new AttrType[inputRelations[j].length-1];
					    			for(int m=0;m<inputRelations[j].length-1;m++){
					    				tempAttr[attrIndex++] = inputRelations[j][m];
					    			}
									FileScan am2 = new FileScan(relationNames.get(j)+".in", tempAttr, stringSizes[j],(short) (inputRelations[j].length-1), inputRelations[j].length-1, tProjection, expr2);
									//new IndexScan(new IndexType(IndexType.B_Index), fileNames[relation], indexNameList[relation], inputRelations[relation], stringSizes[relation], inputRelations[relation].length, inputRelations[relation].length, tProjection, expr, joinColumns[relation]+1, false);
									Iterator itr3= null;
									itr3 = new AdvancedSort(tempAttr, (short) (inputRelations[j].length-1), stringSizes[j],am2, (inputRelations[j].length-1),new TupleOrder(TupleOrder.Descending), 4, 10);
									Tuple t1;
									//System.out.println("@@@@@@@ third else case @@@@@@@@@");
									while((t1 =itr3.get_next())!=null){
										//t1.print(inputRelations[j]);
										Tuple newTuple = new Tuple();
										newTuple.setHdr((short)attrCount, interAttr, strSizes);
										updateTuple(tuple,newTuple, relation, tupleOffset,1);
										int tupleOffset2= getTupleOffset(j);
										updateTuple(t1,newTuple, i, tupleOffset2,1);
										for(int l=0;l<numberOfTables;l++){
											if(newTuple.getStrFld(joinColumns[l]+getTupleOffset(l)+1)!=null){
												bestScore += newTuple.getFloFld(getTupleOffset(l)+inputRelations[l].length-1);
												worstScore += newTuple.getFloFld(getTupleOffset(l)+inputRelations[l].length-1);
											}
											else{
												bestScore += scorePerRelation[l];
											}
											
										}
										
										newTuple.setFloFld(attrCount-1, worstScore);
										newTuple.setFloFld(attrCount-2, bestScore);
										newTuple.setStrFld(attrCount, key);
										//newTuple.print(interAttr);
										/*CondExpr[] expr4 = new CondExpr[2];
										IndexScan dupInterScan1 = new IndexScan(new IndexType(IndexType.B_Index), "DupCheckTopNRAJoin.in", "DupBTreeIndex", dupInterAttr, strSizes, (numberOfTables+1), (numberOfTables+1), dupTProjection, expr4, 1, false);
										System.out.println("**************DupInternscan******************");
										while((t1 =dupInterScan1.get_next())!=null){							
											t1.print(dupInterAttr);
										}*/
										if(minTopK<bestScore){
											RID insertRid1=interFile.insertRecord(newTuple.getTupleByteArray());
											Tuple dupFileTemp = new Tuple();
											dupFileTemp.setHdr((short)(numberOfTables+1), dupInterAttr, strSizes);
											dupFileTemp.setStrFld(1,key);
											dupFileTemp.setIntFld((relation+2),1);
											dupFileTemp.setIntFld((j+2),1);
											//System.out.println("prtinting before inserting ");
											//dupFileTemp.print(dupInterAttr);
											RID rid5=dupCheckIndexFile.insertRecord(dupFileTemp.getTupleByteArray());
											dupBtf.insert(new StringKey(key), rid5);
										}
										/*IndexScan dupInterScan2 = new IndexScan(new IndexType(IndexType.B_Index), "DupCheckTopNRAJoin.in", "DupBTreeIndex", dupInterAttr, strSizes, (numberOfTables+1), (numberOfTables+1), dupTProjection, expr4, 1, false);
										System.out.println("**************DupInternscan******************");
										while((t1 =dupInterScan2.get_next())!=null){							
											t1.print(dupInterAttr);
										}*/
										
										
									}
									itr3.close();
									System.out.println("@@@@@@@ ENDDDD third else case @@@@@@@@@");
									
									
								}
							}
						}
			    break;
			    }
			}
			printTuples1();
		} catch (Exception e) {
			e.printStackTrace();
		}	
		}
		
	}
	
	private void createTopKTuples() {
		
		Tuple tuple = new Tuple();
		RID rid = new RID();
		RID ridScan = new RID();
		int count = 0;
		interTuple = new Tuple();
		int strSizesCount=0;
		int attrIndex = 0;
		int dupAttrIndex = 0;
		int strCount = 0;
		AttrType attrType = new AttrType(inputRelations[0][joinColumns[0]].attrType);
		Scan fileScans[] = new Scan[numberOfTables];
		IndexScan dupInterScan = null;
		IndexScan interScan = null;

		//get Attribute count
		for(int i=0;i<inputRelations.length;i++){
			//Added to store score as  a field
			attrCount+=inputRelations[i].length;
		}
		//System.out.println("attrCount "+attrCount);
		//count of visited relations is stored in an integer variable
		//attrCount is incremented to store best score and worst score
		attrCount+=3;
		//System.out.println("attrCount "+attrCount);
		tProjection = new FldSpec[attrCount];
		dupTProjection = new FldSpec[(numberOfTables+1)];
		for (int i = 0; i < attrCount; i++)
			tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
		for (int i = 0; i < (numberOfTables+1); i++)
			dupTProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
		scorePerRelation= new float[numberOfTables];
		interAttr = new AttrType[attrCount];
		//get string sizes count
		for(int i =0;i<stringSizes.length;i++){
			for(int j=0;j<stringSizes[i].length;j++){
				strCount++;
			}
		}
		strSizes = new short[strCount+1];//string size is set +1 than total number in all relations as there is 
		//an extra column called key in interTuple which is of type string. 
		int strIndex =0;
		//get string sizes for intermediate tuple
		for(int i =0;i<stringSizes.length;i++){
			for(int j=0;j<stringSizes[i].length;j++){
				strSizes[strIndex++]=stringSizes[i][j];
			}
		}
		strSizes[strIndex]=strSizes[0];
		//get attribute types for intermediate tuple
		for(int i=0;i<inputRelations.length;i++){
			for(int j=0;j<inputRelations[i].length;j++){
				interAttr[attrIndex++] = inputRelations[i][j];
			}
			//interAttr[attrIndex++]= new AttrType(AttrType.attrReal);
		}
		//these two are added to store best score and worst score
		interAttr[attrIndex++]= new AttrType(AttrType.attrReal);
		interAttr[attrIndex++]= new AttrType(AttrType.attrReal);
		interAttr[attrIndex]= new AttrType(AttrType.attrString); //this is wer key of every inter tuple is stroed.
		//create duplicate file tuple header
		dupInterAttr = new AttrType[numberOfTables+1];
		//dupInterAttr[dupAttrIndex++]= new AttrType(AttrType.attrInteger);
		dupInterAttr[dupAttrIndex++]= new AttrType(AttrType.attrString); //Key is string
		for (int i = 0; i < numberOfTables; i++) {
			dupInterAttr[dupAttrIndex++]= new AttrType(AttrType.attrInteger);
		}
		
		
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
		//check with jyothi how to create index on string?
		//how is their code working for given excel data.
		
	    
	    try {
	    	int topKCounter=0;
			do{
				for (int i = 0; i < numberOfTables; i++) {
					int tupleOffset = getTupleOffset(i);
					tuple = new Tuple();
					tuple = iterators[i].get_next();
					/*ridScan = ConstantVars.getGlobalRID();
					String rid2 = Integer.toString(ridScan.pageNo.pid)+"_"+Integer.toString(ridScan.slotNo);
					System.out.println("@@@@@@@@@@ RID is : "+rid2);
					System.out.println("RID is : "+iterators[i]);*/
					
					/*System.out.println("@@@@@@@@@@  at start");
					tuple.print(inputRelations[i]);*/
					scorePerRelation[i] = tuple.getFloFld(inputRelations[i].length-1); //gets the score from the tuple
					//this is used to store the current score for an iterattion. this is used to calculate bestscores for intertuples which
					//have corresponding other relations as blank.
					//tuple.print(inputRelations[i]);
					//System.out.println("Tuple: "+ tuple);
					//System.out.println("In Index scan" + tuple.getIntFld(1));
					boolean newTupleFlag=true;
					try {
					      btf = new BTreeFile("BTreeIndex", attrType.attrType, strSizes[0], 1); 
					      dupBtf = new BTreeFile("DupBTreeIndex", attrType.attrType, strSizes[0], 1);
					    }
					    catch (Exception e) {
					      //status = FAIL;
					      e.printStackTrace();
					      Runtime.getRuntime().exit(1);
					    }
					    Scan scan = null;
					    Scan dupScan = null;
					    
					    try {
					      scan = new Scan(interFile);
					      dupScan = new Scan(dupCheckIndexFile);
						}
						catch (Exception e) {
						  //status = FAIL;
						  e.printStackTrace();
						  Runtime.getRuntime().exit(1);
						}
					numOfScanned[i]++;
					t= new Tuple();
					t.setHdr((short)attrCount, interAttr, strSizes);
					switch (attrType.attrType) {
					
					case AttrType.attrString:
						Tuple tt = new Tuple();
					    tt.setHdr((short)attrCount, interAttr, strSizes);
					    Tuple duptt = new Tuple();
					    duptt.setHdr((short)(numberOfTables+1), dupInterAttr, strSizes);
					    RID scanRid = new RID();
					    RID dupScanRid = new RID();
					    String tupleKey =null;
					    String dupTupleKey =null;
					    Tuple temp = null;
					    Tuple dupTemp = null;
					    
					    
					    try {
					      temp = scan.getNext(scanRid);
					      dupTemp = dupScan.getNext(dupScanRid);
					    }
					    catch (Exception e) {
					      e.printStackTrace();
					    }
					    while ( temp != null) {
					      tt.tupleCopy(temp);
					      
					      try {
					    	  tupleKey = tt.getStrFld(attrCount);
					      }
					      catch (Exception e) {
						e.printStackTrace();
					      }
					      
					      try {
					    	  //btree index is xreated
					    	  /*tt.print(interAttr);
					    	  System.out.println("tuplekey "+tupleKey);*/
						btf.insert(new StringKey(tupleKey), scanRid); 
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
					    
					    while ( dupTemp != null) {
						      duptt.tupleCopy(dupTemp);
						      
						      try {
						    	  dupTupleKey = duptt.getStrFld(joinColumns[0]+1);
						      }
						      catch (Exception e) {
						    	  e.printStackTrace();
						      }
						      
						      try {
						    	  //btree index is xreated
						    	  dupBtf.insert(new StringKey(dupTupleKey), dupScanRid); 
						      }
						      catch (Exception e) {
						    	  e.printStackTrace();
						      }
						      try {
						    	  dupTemp = dupScan.getNext(dupScanRid);
						      }
						      catch (Exception e) {
						    	  e.printStackTrace();
						      }
						    }
						    dupScan.closescan();
					    //create btree file, then a scan for it, open scan read join column, put this as key in index 
					    String key = tuple.getStrFld(joinColumns[i]+1);
						interTuple.setStrFld(joinColumns[0]+1, key);
						boolean too = true;
						Tuple dup2 = new Tuple();
						dup2.setHdr((short)(numberOfTables+1), dupInterAttr, strSizes);
						CondExpr[] expr = new CondExpr[2];
						expr[0] = new CondExpr();
						expr[0].op = new AttrOperator(AttrOperator.aopEQ);
						expr[0].type1 = new AttrType(AttrType.attrSymbol);
						expr[0].type2 = new AttrType(AttrType.attrString);
						expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
						expr[0].operand2.string = key;
						expr[0].next = null;
						expr[1] = null;
						
						//expr=null;
						dupInterScan = new IndexScan(new IndexType(IndexType.B_Index), "DupCheckTopNRAJoin.in", "DupBTreeIndex", dupInterAttr, strSizes, (numberOfTables+1), (numberOfTables+1), dupTProjection, expr, 1, false);
						interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, attrCount, false);
						RID dupTempRID;
						HashMap<String, Boolean> dupRandomMap = new HashMap<String, Boolean>();
						RID tempRID;
						HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
						
						
							//this block should be entered when key is present in dup				

							/*
							 * this while will run as many times as there are records in dupIndex
							 *  heapfile with matching key.  here if Relation is set as true ,then we make a 
							 *  copy of that tuple and insert into heap file
							 *  
							 *  else we set the currently present relation's corresponindg int value as 1.
							 */
							bestScore=0;
							worstScore=0;
							dup2 = dupInterScan.get_next();
							if ((dup2) != null) {
								/*System.out.println("in dup");
								dup2.print(dupInterAttr);*/
								dupTempRID = dupInterScan.getRID();
								RID currRID = dupInterScan.getRID();
								/*
								 * write an if else here
								 * if rel 1 is visted as true , now u r in relation 2, then dupheap file set flag for rel 2 as true.
								 * else again u r seeing rel 1 then make a duplicate.
								 */
								
								//How to handle expopnentially adding duplicate tuples? Is it by using this hash map?
								String scanKey = "" + currRID.pageNo.pid + "_"+ currRID.slotNo;
								if (dupRandomMap.containsKey(scanKey)) {
									continue;
								} else {
									dupRandomMap.put(scanKey, true);
								}
								// System.out.println("RID : " +tempRID.pageNo.pid + "\t" + tempRID.slotNo);
								// updateTuple(tuple, dup2, i, tupleOffset,1);
								// dup2.setIntFld((i+1),key);
								
								
								
								int isSet = dup2.getIntFld((i + 2));
								/*if isSet is represents the presence of duplicates & hence copy the tuple values & insert into the 
								interfile*/
								if (isSet == 1) {
									//We are not storing the duplicate tuples in the dupIndex heap file
									/*Tuple dup3 = new Tuple();
									dup3.setHdr((short) (numberOfTables + 1),dupInterAttr, strSizes);
									dup3.tupleCopy(dup2);
									RID insertRid = dupCheckIndexFile.insertRecord(dup3.getTupleByteArray());*/
									
									if((t = interScan.get_next())!=null){
										/*
										 * while is changed to if for eliminating the exponential duplication of tuples in interfile. 
										 * while((t = interScan.get_next())!=null){
										tempRID = interScan.getRID();
										RID currRID1 = interScan.getRID();
										String scanKey1= ""+currRID1.pageNo.pid+"_"+currRID1.slotNo;
										if(randomMap.containsKey(scanKey1)){
											continue;
										}
										else{
											randomMap.put(scanKey1, true);
										}*/
										//System.out.println("RID : " + tempRID.pageNo.pid + "\t" + tempRID.slotNo);
							
																			
										Tuple newTuple = new Tuple();
										newTuple.setHdr((short)attrCount, interAttr, strSizes);
										//updateTuple(t,newTuple, i, tupleOffset,1);
										newTuple.tupleCopy(t);
										/*System.out.println("$$$$After$$$$$$$$");
										newTuple.print(interAttr);*/
										updateTuple(tuple, newTuple, i, tupleOffset,1);
										
										for(int j=0;j<numberOfTables;j++){
											if(newTuple.getStrFld(joinColumns[j]+getTupleOffset(j)+1)!=null){
												//we need to get score of every relation. for that we go through the input relations ;get value 
												//of last column in relation
												bestScore += newTuple.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
												worstScore += newTuple.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
											}
											else{
												bestScore += scorePerRelation[j];
											}
											
										}
										
										newTuple.setFloFld(attrCount-1, worstScore);
										newTuple.setFloFld(attrCount-2, bestScore);
										//newTuple.print(interAttr);
										//t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
										//need to update the best & worst scores here
										/*if isSet is represents the presence of duplicates & hence copy the tuple values & insert into the 
										interfile*/
										//we are handling pruninig condition in the below if case
										if(minTopK<bestScore){
										RID insertRid1=interFile.insertRecord(newTuple.getTupleByteArray());
										}
										printTuples();
									}
																		
								} else {
									//Tuple indexing will start from 1, key is placed at 1st position followed by the value of 1/0 for relations
									//thus increment by i+2
									dup2.setIntFld((i + 2), 1);
									dupCheckIndexFile.updateRecord(dupTempRID, dup2);
									//dup2.print(dupInterAttr);
									while((t = interScan.get_next())!=null){
										tempRID = interScan.getRID();
										RID currRID1 = interScan.getRID();
										String scanKey1= ""+currRID1.pageNo.pid+"_"+currRID1.slotNo;
										if(randomMap.containsKey(scanKey1)){
											continue;
										}
										else{
											randomMap.put(scanKey1, true);
										}
										//System.out.println("RID : " + tempRID.pageNo.pid + "\t" + tempRID.slotNo);
										
										/*System.out.println("update before updating");
										t.print(interAttr);*/
										/*System.out.println("Before update");
										t.print(interAttr);*/
										//tuple.print(inputRelations[i]);
										updateTuple(tuple, t, i, tupleOffset,1);
										bestScore=0.0f;
										worstScore=0.0f;
										for(int j=0;j<numberOfTables;j++){
											if(t.getStrFld(getTupleOffset(j)+joinColumns[j]+1)!=null){
												//we need to get score of every relation. for that we go through the input relations ;get value 
												//of last column in relation
												
												/*
												 * we need to get the offset of each relation in intertuple so we are using getTupleOffset(j).
												 * joinColumn[j+1] will give attribute in that relation.
												 */
												bestScore += t.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
												worstScore += t.getFloFld(getTupleOffset(j)+inputRelations[j].length-1);
											}
											else{
												bestScore += scorePerRelation[j];
											}
											
										}
										//t.setIntFld(attrCount, t.getIntFld(attrCount)+1);
										//need to update the best & worst scores here
										t.setFloFld(attrCount-1, worstScore);
										t.setFloFld(attrCount-2, bestScore);
										//printTuples();
										//System.out.println("update after updating");
										//t.print(interAttr);
										interFile.updateRecord(tempRID, t);
										printTuples();
										
										//see if wwe can delete the reords when pruning cond fails. this will make 
										//file smaller.
									}
								}
								
								
								calcluateMinTopKAndThreshold();
								dupInterScan.close();
								interScan.close();
							}
							
							
						else{
							//there is no key in dupfilecheck index tree . so make an entry into it.
							//Need to write code for updating the best & worst scores for every tuple when a new tuple is found
							Tuple dupFileTemp = new Tuple();
							dupFileTemp.setHdr((short)(numberOfTables+1), dupInterAttr, strSizes);
							//Tuple indexing will start from 1, key is placed at 1st position followed by the value of 1/0 for relations
							//thus increment by i+2
							dupFileTemp.setStrFld(1,key);
							dupFileTemp.setIntFld((i+2),1);
							/*System.out.println("prtinting before inserting ");
							dupFileTemp.print(dupInterAttr);*/
							dupCheckIndexFile.insertRecord(dupFileTemp.getTupleByteArray());
							//tuple.print(inputRelations[i]);
							worstScore = tuple.getFloFld(inputRelations[i].length-1); //gets the score from the tuple
							//System.out.println("worstScore ="+worstScore);
							for(int j=0; j <numberOfTables ; j++){
								if(j==i)
									continue;
								else
									bestScore = bestScore +scorePerRelation[j];
							}
							bestScore+=worstScore;
							//minTopK
							//threshold
							Tuple newTuple = new Tuple();
							newTuple.setHdr((short)attrCount, interAttr, strSizes);
							
														
							updateTuple(tuple,newTuple, i, tupleOffset,1);
							
							//newTuple.setStrFld(getTupleOffset(i)+joinColumns[i]+1, key);
							newTuple.setFloFld(attrCount-1, worstScore);
							newTuple.setFloFld(attrCount-2, bestScore);
							newTuple.setStrFld(attrCount, key);
							/*System.out.println("this is new tuple");
							newTuple.print(interAttr);*/
							//we are handling pruninig condition in the below if case
							if(minTopK<bestScore){
								RID insertRid=interFile.insertRecord(newTuple.getTupleByteArray());
								printTuples();
								
							}						
							//updateAllScoresStringJoin();
							//calcluateMinTopKAndThreshold();
						}
					    break;//end of case integer
					}
				updateAllScoresStringJoin();
				calcluateMinTopKAndThreshold();
				//System.out.println("&&&&&&&&&&&&&&&&&&& After calculate &&&&&&&&&&&&&&777");
				
				/*
				 * B tree Index file is closed here since in the next iteration a new B tree file is again created, this will save memory
				 */
				try {
					btf.close();
					dupBtf.close();
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				topKCounter++;
				}//end of for loop
			//System.out.println("!!!!!!!!!!!!!!!!!exiting condition "+threshold+" min top k "+minTopK);
			/*boolean a =!(threshold<=minTopK);
			boolean b= (topKCounter<=topK*2);
			boolean c = a&b;
			boolean d = a&&b;
			System.out.println("!!!!!!!!!!!!!!!!!exiting condition Threshold="+threshold+" minTopK="+minTopK +" topKCounter ="+topKCounter+" A and B : "+a + " "+b+ " "+c+ " "+d );*/
			}while((!(threshold<=minTopK)) || (topKCounter<=topK*2));//this is the exit condition. 
			printTuples1();			
			
			/*
			 * that is when threshold is less than min top k.
			 * threshold = min(best score of all tuples) which is max of unseen
			 * minTopK = min(worst score of top k tuples)
			 *  if the best score of any tuple is less than worst score of top k tuples 
			 *  it means that those tuples can't become part of the top k tuples.
			 */
			//System.out.println("!!!!!!!!!!!!!!!!!exiting condition "+threshold+" min top k "+minTopK);
			
			//write into outFile
			
			
		}  catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	public void DeleteTopNRAJoin(Iterator iter,int relation){
		/*while((t1 =am.get_next())!=null){
		t1.print(inputRelations[tableNum]);
		}
		printTuples();*/
		Tuple tuple = new Tuple();
		IndexScan interScan = null;
		AttrType attrType = inputRelations[relation][joinColumns[relation]];
		HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
		
		try{
			System.out.println("Before delete " + interFile.getRecCnt());
			while((tuple=iter.get_next())!=null){
				RID temprid=new RID();
				//Get the tuple's key
				String key="";
				if(attrType.attrType==AttrType.attrInteger){
					key = String.valueOf(tuple.getIntFld(joinColumns[relation]+1));
				}
				else{
					key = tuple.getStrFld(joinColumns[relation]+1);
				}

				//Condition for scanning the original relation
				CondExpr[] expr = new CondExpr[2];
				expr[0] = new CondExpr();
				expr[0].op = new AttrOperator(AttrOperator.aopEQ);
				expr[0].type1 = new AttrType(AttrType.attrSymbol);
				expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
				if(attrType.attrType==AttrType.attrInteger){
					expr[0].type2 = new AttrType(AttrType.attrInteger);
					expr[0].operand2.integer = Integer.parseInt(key);
				}
				else{
					expr[0].type2 = new AttrType(AttrType.attrString);
					expr[0].operand2.string= key;
					//System.out.println("String key : " + key);
				}			
				expr[0].next = null;
				expr[1] = null;
				
				Tuple tempTuple =new Tuple();
				tempTuple.setHdr((short)attrCount, interAttr, strSizes);
				interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, attrCount, false);
				String key1="";
				while((tempTuple =interScan.get_next())!=null){
					RID currRID1 = interScan.getRID();
					temprid = ConstantVars.getGlobalRID();
					String scanKey1= ""+currRID1.pageNo.pid+"_"+currRID1.slotNo;
					if(randomMap.containsKey(scanKey1)){
						continue;
					}
					else{
						randomMap.put(scanKey1, true);
					}
					
					if(attrType.attrType==AttrType.attrInteger){
						key1 = String.valueOf(tempTuple.getIntFld(joinColumns[relation]+1));
					}
					else{
						key1 = tempTuple.getStrFld(joinColumns[relation]+1);
					}
					if(key1.equalsIgnoreCase(key)){
						int tupleOffset = getTupleOffset(relation);
						boolean isSame = true;
						for(int i=tupleOffset;i<inputRelations[relation].length-1;i++){
							AttrType attrType1 = inputRelations[relation][i];
							switch(attrType1.attrType){
							  case AttrType.attrInteger:
								  if(tuple.getIntFld(i+1-tupleOffset)!=tempTuple.getIntFld(i+1))
								  isSame = false;
								  break;
							  case AttrType.attrReal:
								  if(tuple.getFloFld(i+1-tupleOffset)!=tempTuple.getFloFld(i+1))
								  isSame = false;
								  break;
							  case AttrType.attrString:
								  String a =tuple.getStrFld(i+1-tupleOffset);
								  String b=tempTuple.getStrFld(i+1);
								  if(!(a.equals(b)))
								  	isSame = false;
								  break;
							  }
						}
						if(isSame){
							//System.out.println("TUPLES ARE SAME in delete intertuple");
							//tempTuple.print(interAttr);
							tempTuple.setStrFld(attrCount, "DEL");
							if(attrType.attrType==AttrType.attrInteger){
								tempTuple.setIntFld(attrCount, 555);
							}
							else{
								//System.out.println("DEL Testing");
								tempTuple.setStrFld(attrCount, "DEL");
							}
							interFile.updateRecord(temprid, tempTuple);
							//interFile.deleteRecord(temprid);	
							//deleteFromInterFile(temprid,relation);
							//interScan.close();
							//interScan = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, expr, attrCount, false);
						}						
					}
				}
				//interScan.close();
				/*IndexScan tempIndex = new IndexScan(new IndexType(IndexType.B_Index), fileNames[relation], indexNameList[relation], inputRelations[relation], stringSizes[relation], inputRelations[relation].length, inputRelations[relation].length, tProjection, expr, joinColumns[relation]+1, false);
				Tuple tempTuple = tempIndex.get_next();
				RID temprid=new RID();
				while(tempTuple!=null){
					temprid = ConstantVars.getGlobalRID();
					if(tuplesMatch(tuple,tempTuple,inputRelations[relation]))
						break;
					tempTuple = tempIndex.get_next();
				}*/
				
				//deleteFromInterFile(temprid,relation);
			}
			hardDelete();
			System.out.println("After delete " + interFile.getRecCnt());
		}
		catch(Exception e){
			System.out.println("Error in deleteTuple");
			e.printStackTrace();
		}
		//printTuples1();
		
	}
	
	/*private void deleteFromInterFile(RID delRID, int relation){
		try{
			System.out.println("Before delete " + interFile.getRecCnt());
			int rid = delRID.pageNo.pid*1000 + delRID.slotNo;
			int colNum = getTupleOffset(relation)+inputRelations[relation].length;
			System.out.println("Index scan on the colNum " + colNum + " on RID : " + rid);
			CondExpr[] expr = new CondExpr[2];
			expr[0] = new CondExpr();
			expr[0].op = new AttrOperator(AttrOperator.aopEQ);
			expr[0].type1 = new AttrType(AttrType.attrSymbol);
			expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), colNum+1);
			expr[0].type2 = new AttrType(AttrType.attrInteger);
			expr[0].operand2.integer = rid;			
			expr[0].next = null;
			expr[1] = null;
			expr=null;
			IndexScan interIndexScan = new IndexScan(new IndexType(IndexType.B_Index),"InterTuple.in","BTreeIndex",interAttr, strSizes, attrCount, attrCount, tProjection,expr,attrCount,false);
			Tuple delTuple = interIndexScan.get_next();
			while(delTuple!=null){
				RID tempRID = ConstantVars.getGlobalRID();
				int rid1 = tempRID.pageNo.pid*1000 + tempRID.slotNo;
				if(rid==rid1){
					System.out.println("Deleting record id " + tempRID.pageNo + ":" + tempRID.slotNo);
					interFile.deleteRecord(tempRID);
					break;
						
				}
				delTuple = interIndexScan.get_next();
			}
			interIndexScan.close();
			System.out.println("After delete " + interFile.getRecCnt());
		}
		catch(Exception e){
			System.out.println("Error in deleteFromInterFile");
			e.printStackTrace();
		}
	}*/

	
	private boolean tuplesMatch(Tuple t1, Tuple t2, AttrType[] tupleAttrs){
		boolean flag=true;
		try{
			for(int i=0;i<tupleAttrs.length;i++){
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
	
	//used to copy conteents from 1 tuple to another when both have different header and we just need content.
	//example in  interTuple we need to copy content from every relation to inter tuple.
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
	
	public void updateAllScoresStringJoin(){}
	
	/*public void updateAllScoresStringJoin1(){
		IndexScan am = null;
		 try {
			 //we used indexscan as we need RID and filescan will not give RID. each is ready in while loop ,updated with score and
			 //stroed back in intrtuple. for this we need RID. 
			 
			 //indexscan is passed with no condEXpr . so we hope all records will be scanned.
		      am = new IndexScan(new IndexType(IndexType.B_Index), "InterTuple.in", "BTreeIndex", interAttr, strSizes, attrCount, attrCount, tProjection, null, attrCount, false);
				
		      
		      /*Tuple t1;
				while((t1 =am.get_next())!=null){
					t1.print(attrTypeList[k]);
				}
		      Tuple t1=null;
		      RID tempRID = null;
		      float bestScore1=0.0f,worstScore1=0.0f;
		      HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
		      
		      while((t1 = am.get_next()) != null){
		    	  bestScore1=0.0f;
		    	  worstScore1=0.0f;
		    	  //System.out.println("inside update all 1");
		    	  //t1.print(interAttr);
		    	  tempRID = am.getRID(); 
		    	  RID currRID1 = am.getRID();
		    	  String scanKey1= ""+currRID1.pageNo.pid+"_"+currRID1.slotNo;
					if(randomMap.containsKey(scanKey1)){
						continue;
					}
					else{
						randomMap.put(scanKey1, true);
					}
					//System.out.println("RID : " + tempRID.pageNo.pid + "\t" + tempRID.slotNo);
					
					for(int i=0;i<numberOfTables;i++){
						String a =t1.getStrFld(getTupleOffset(i)+joinColumns[i]+1);
						if(!(a==null || a.equals(""))){
							//we need to get score of every relation. for that we go through the input relations ;get value 
							//of last column in relation
							bestScore1 += t1.getFloFld(getTupleOffset(i)+inputRelations[i].length-1);
							worstScore1 += t1.getFloFld(getTupleOffset(i)+inputRelations[i].length-1);
						}
						else{
							bestScore1 += scorePerRelation[i];
							float n = bestScore1;
									
						}
					}
					/*System.out.println("inside update all 2");
					t1.print(interAttr);
			    	t1.setFloFld(attrCount-1, worstScore1);
					t1.setFloFld(attrCount-2, bestScore1);
					interFile.updateRecord(tempRID, t1);
					System.out.println("inside updateAllScores");
					//printTuples();
				}
							      
		    } 
		    catch (Exception e) {
			   //status = false;
			   e.printStackTrace();
			 }
	}*/
	
	public void calcluateMinTopKAndThresholdOld(){}
	/*public void calcluateMinTopKAndThresholdOld1(){
		
		//Start: find minTopK
		
		Iterator am = null;
		 try {
		      am  = new FileScan("InterTuple.in", interAttr, strSizes,(short)attrCount, attrCount,tProjection, null);
		      
		      Tuple t1;
				while((t1 =am.get_next())!=null){
					t1.print(attrTypeList[k]);
				}
							      
		    } 
		    catch (Exception e) {
			   //status = false;
			   System.err.println (""+e);
			 }

		Iterator itr=null;
		try {
			itr = new Sort(interAttr, (short)attrCount, strSizes,am, attrCount-1,new TupleOrder(TupleOrder.Ascending), 4, n_buf_pgs);
			Tuple t1 =null;
			if((t1 = itr.get_next()) != null){
				minTopK = t1.getFloFld(attrCount-1);
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		//End: find minTopK
		
		//Start: find threshold
		try {
			itr = new Sort(interAttr, (short)attrCount, strSizes,am, attrCount-2,new TupleOrder(TupleOrder.Ascending), 4, n_buf_pgs);
			Tuple t1 =null;
			if((t1 = itr.get_next()) != null){
				threshold = t1.getFloFld(attrCount-2);
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		//End: find threshold
		
	}*/

	
	public void hardDelete(){
		Iterator am = null;
		try {
			System.out.println("%%%%%%%%% Following Tuples are deleted %%%%%%%%");
			CondExpr[] expr = new CondExpr[2];
			expr[0] = new CondExpr();
			expr[0].op = new AttrOperator(AttrOperator.aopEQ);
			expr[0].type1 = new AttrType(AttrType.attrSymbol);
			expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), attrCount);
			expr[0].next = null;
			expr[1] = null;
			expr[0].type2 = new AttrType(AttrType.attrString);
			expr[0].operand2.string= "DEL";
			/*if(interAttr[attrCount].attrType==AttrType.attrInteger){
				expr[0].type2 = new AttrType(AttrType.attrInteger);
				expr[0].operand2.integer = 555;
			}
			else{
				expr[0].type2 = new AttrType(AttrType.attrString);
				expr[0].operand2.string= "DEL";				
			}*/
			//expr=null;
			am = new FileScan("InterTuple.in", interAttr, strSizes,(short) attrCount, attrCount, tProjection, expr);
			Tuple t2 = null;
			RID tempRID =null;
			while ((t2 = am.get_next()) != null) {
		        t2.print(interAttr);
		        tempRID=ConstantVars.getGlobalRID();
		        interFile.deleteRecord(tempRID);
		        //System.out.println("t2.getScore()"+t2.getScore());
		    }
			am.close();
		} catch (Exception e) {
			// status = false;
			System.err.println("" + e);
		}
		printTuples1();

	}
	
	public void calcluateMinTopKAndThreshold() throws JoinsException, SortException, IndexException, IOException{
		//Start: find minTopK
		Iterator am = null;
		Iterator am1 = null;
		Iterator it1=null;
		 try {
		      am  = new FileScan("InterTuple.in", interAttr, strSizes,(short)attrCount, attrCount,tProjection, null);
		      am1  = new FileScan("InterTuple.in", interAttr, strSizes,(short)attrCount, attrCount,tProjection, null);
		      /*Tuple t1;
				while((t1 =am.get_next())!=null){
					t1.print(attrTypeList[k]);
				}*/
			} 
		    catch (Exception e) {
			   //status = false;
			   System.err.println (""+e);
			 }

		Iterator itr=null;
		try {
			Tuple t1 =null;
			it1 = new Sort(interAttr, (short)attrCount, strSizes,am, attrCount-1,new TupleOrder(TupleOrder.Descending), 4, n_buf_pgs);
			int itr1=1;
			while ((t1 = it1.get_next()) != null) {
				//System.out.println("&&& BEFORE SETTING Min top k : "+minTopK+ "&&&");
				if(itr1==topK){
					minTopK = t1.getFloFld(attrCount-1);
					//System.out.println("&&& Min top k : "+minTopK+ "&&&");
					break;
				}
				itr1++;				
			}
			//it1.close();
			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		am.close();
		//End: find minTopK
		
		//Start: find threshold
		try {
			itr = new Sort(interAttr, (short)attrCount, strSizes,am1, attrCount-2,new TupleOrder(TupleOrder.Ascending), 4, n_buf_pgs);
			Tuple t1 =null;
			if((t1 = itr.get_next()) != null){
				threshold = t1.getFloFld(attrCount-2);
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		am1.close();
		
		//End: find threshold
		
	}

	public void getTopK() throws JoinsException, SortException, IndexException, IOException{
		
		FileScan am = null;
		FileScan amTest = null;
		//System.out.println("in get top k");
		 try {
		      am  = new FileScan("InterTuple.in", interAttr, strSizes,(short)attrCount, attrCount,tProjection, null);
		      amTest  = new FileScan("InterTuple.in", interAttr, strSizes,(short)attrCount, attrCount,tProjection, null);
		      
		      Tuple t1;
				while((t1 =amTest.get_next())!=null){
					t1.print(interAttr);
				}
		      //System.out.println("in get top k 2");
								      
		    } 
		    catch (Exception e) {
			   //status = false;
			   System.err.println (""+e);
			 }

		Iterator itr=null;
		try {
			//attrcount-1 =bestscore will be same as attrcount-2=worstscore
			itr = new Sort(interAttr, (short)attrCount, strSizes,am, attrCount-1,new TupleOrder(TupleOrder.Descending), 4, n_buf_pgs);			
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		am.close();
		amTest.close();
		Tuple tuple1;
		System.out.println("****************Start of Result***********************");
		while (topK > 0) {
			try {
				//System.out.println("in get top k top k"+topK);
				topK--;
				if ((tuple1 = itr.get_next()) != null) {
					tuple1.print(interAttr);
					//System.out.println("in get top k top k"+topK);
				}				
		}catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		}
		itr.close();
		System.out.println("****************End of Result***********************");
		
	}
	
	/*public void getTopKWihtoutSort(){
		
		Iterator am = null;
		//System.out.println("in get top k");
		 try {
			am = new FileScan("InterTuple.in", interAttr, strSizes,(short) attrCount, attrCount, tProjection, null);
			Tuple t1;
			System.out.println("****************Start of Result***********************");
			int itr=1;
			while ((t1 = am.get_next()) != null) {
				t1.print(interAttr);
				if(itr==topK){
					break;
				}
				itr++;				
			}
			System.out.println("****************End of Result***********************");								      
		    } 
		    catch (Exception e) {
			   //status = false;
			   System.err.println (""+e);
			}
	}*/
	
	public void printTuples(){}
	public void printTuples1(){
		System.out.println("\n\n$$$$$$$$$$$$$$$$$$$$$ START OF TOP K TUPLES $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");
		try {
			Iterator am  = new FileScan("InterTuple.in", interAttr, strSizes,(short)attrCount, attrCount,tProjection, null);
			Tuple tuple1 = null;
			Iterator it1 = null;
			try {
				it1 = new Sort(interAttr, (short)attrCount, strSizes,am, attrCount-1,new TupleOrder(TupleOrder.Descending), 4, n_buf_pgs);
				int count=0;
				while((tuple1 = it1.get_next()) != null) {
					if(count<topK)
					tuple1.print(interAttr);
					else
						break;
					count++;
				}
				//it1.close();
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			am.close();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		System.out.println("$$$$$$$$$$$$$$$$$$$$$ END OF TOP K TUPLES $$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");
		
	}

}
