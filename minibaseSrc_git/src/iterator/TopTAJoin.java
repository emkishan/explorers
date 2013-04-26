package iterator;

import global.AttrOperator;
import global.AttrType;
import global.ConstantVars;
import global.GlobalConst;
import global.IndexType;
import global.RID;
import global.TupleOrder;
import heap.HFBufMgrException;
import heap.HFDiskMgrException;
import heap.HFException;
import heap.Heapfile;
import heap.Scan;
import heap.Tuple;
import index.IndexScan;

import java.io.IOException;
import java.util.HashSet;

import btree.BTreeFile;
import btree.IntegerKey;


public class TopTAJoin {
	private int numberOfTables;
	private AttrType inputRelations[][];
	private int lengths[];
	private short[][] stringSizes;
	private int joinColumns[];
	private Iterator iterators[],tempIterators[];
	private String indexNames[];
	private CondExpr[] outFilter;
	private int knumberOfTuples;
	private FldSpec[] proj_list;
	private Tuple innerTuples[];
	private int n_buf_pgs;
	private int numOutputFlds;
	private Tuple JTuple;
	private int numOfScanned[], numOfProbed[];
	private Heapfile heapFiles[], outFile;
	private RID fileRid,minRID;
	private String[] indexFileNames;
	private boolean duplFlag;
	private String[] fileNames;
	private float threshold;
	private float min;
	private Heapfile kResultsFile,interTAtuples;
	private AttrType[] attrTypes,superAttrTypes,combinedAttrTypes;
	private int[] tupleOffsets,superOffsets;
	private int mainRelNum;
	private Tuple combinedTuple = new Tuple();
	private Tuple tupleCopy = new Tuple();
	private Tuple finalTuple = new Tuple();
	private Tuple superTuple;
	private HashSet<Integer> readRIDs,readIntKeys;
	private HashSet<String> readStrKeys;
	private short[] tempStringSizes,superStrSizes;
	private float mainTupleScore;
	private BTreeFile[] interBTF;
	private String[] interIndexName,interFileName;
	private IndexType[] interIndexType;
	private float[] kMinimums;

	//
	public TopTAJoin (int numTables,
			AttrType[][] in,
			int[] len_in,
			short[][] s_sizes,
			int[] join_col_in,
			Iterator[] am,
			String[] indexNames,
			int amt_of_mem,
			CondExpr[] outFilter,
			FldSpec[] proj_list,
			int n_out_flds,
			int num, 
			String[] fileNames,
			boolean duplicates){

		try{
			numberOfTables = numTables;
			inputRelations = new AttrType[numTables][];
			indexFileNames = new String[fileNames.length];
			joinColumns=join_col_in;
			outFile = null;
			iterators = am;
			duplFlag = duplicates;
			tupleOffsets = new int[numTables+1];
			minRID = new RID();
			this.indexNames = new String[indexNames.length];
			readRIDs = new HashSet<Integer>();
			readStrKeys = new HashSet<String>();
			readIntKeys = new HashSet<Integer>();
			superTuple = new Tuple();
			kMinimums = new float[numTables];
			
			//min = numberOfTables;

			//Setting minimum to number of Relations as it is max possible value
			threshold = numTables;

			for(int i=0;i<fileNames.length;i++){
				indexFileNames[i] = fileNames[i];
			}

			for(int i=0;i<indexNames.length;i++){
				this.indexNames[i] = indexNames[i];
			}

			int totalCount=0;
			for(int i=0;i<in.length;i++){
				totalCount += in[i].length;
				//RID of each record
				totalCount++;
			}
			//RID of full record and combined score
			totalCount += 1;

			superAttrTypes = new AttrType[totalCount];
			combinedAttrTypes = new AttrType[totalCount+1];
			int superCount=0;
			superOffsets = new int[numTables];
			for(int i=0;i<in.length;i++){
				superOffsets[i]=superCount;
				for(int k=0;k<in[i].length;k++){
					superAttrTypes[superCount++] = in[i][k];
				}
				superAttrTypes[superCount++]=new AttrType(AttrType.attrInteger);
			}
			superAttrTypes[superCount++] = new AttrType(AttrType.attrReal);

			for(int k=0;k<totalCount-1;k++){
				combinedAttrTypes[k] = superAttrTypes[k];
			}
			combinedAttrTypes[totalCount-1] = new AttrType(AttrType.attrInteger);
			combinedAttrTypes[totalCount] = new AttrType(AttrType.attrReal);
			
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
			tempIterators = new Iterator[am.length];
			for (int i = 0; i < numTables; i++) {
				iterators[i] = am[i];
				tempIterators[i] = am[i];
			}

			innerTuples = new Tuple[numTables];

			// Copy the String sizes and initialize tuples
			stringSizes = new short[s_sizes.length][];
			int superStrSize = 0;
			//innerTuples = new
			for (int i = 0; i < numTables; i++) {
				stringSizes[i] = s_sizes[i];
				superStrSize += s_sizes[i].length;
				//innerTuples[i] = new Tuple();
			}

			superStrSizes = new short[superStrSize];
			for(int i=0;i<superStrSize;i++)
				superStrSizes[i] = 30;

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

			int count = 0;
			int prevRel = 0;
			tupleOffsets[0]=0;
			/*for(int i=0;i<proj_list.length;i++){
				this.proj_list[i] = proj_list[i];
				if(prevRel!=this.proj_list[i].relation.key){
					tupleOffsets[prevRel+1] = count;
					prevRel = this.proj_list[i].relation.key;
				}
				count++;
			}
			tupleOffsets[prevRel+1] = this.proj_list.length;*/
			
			for(int i=0;i<proj_list.length;i++){
				this.proj_list[i] = proj_list[i];
				/*if(prevRel!=this.proj_list[i].relation.key){
					tupleOffsets[prevRel+1] = count;
					prevRel = this.proj_list[i].relation.key;
				}*/
				count++;
			}
			//tupleOffsets[prevRel+1] = this.proj_list.length;
			count=0;
			for(int i=0;i<numberOfTables;i++){
				tupleOffsets[i]=count;
				count += inputRelations[i].length;
				count++;
			}
			tupleOffsets[numberOfTables] = count;
		}



		catch(Exception e){
			System.out.println("Exception in constructor");
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
				interBTF[i] = new BTreeFile("interTATuples" + i +"_BTreeIndex", AttrType.attrInteger,GlobalConst.INDEX_REC_LEN,1);
				interIndexType[i] = new IndexType(IndexType.B_Index);
				interIndexName[i] = "interTATuples" + i + "_BTreeIndex";
				interFileName[i] = "interTATuples.in";
			}

			Scan s = new Scan(interTAtuples);
			Tuple temp = null;
			RID rid1 = new RID();
			temp = s.getNext(rid1);
			Tuple t = new Tuple();
			t.setHdr((short)superAttrTypes.length,superAttrTypes,superStrSizes);
			while(temp!=null){
				//System.out.println("Tuple is ");
				//temp.print(superAttrTypes);
				for(int i=0;i<numberOfTables;i++){
					int column = superOffsets[i]+inputRelations[i].length+1;
					temp.setHdr((short)(superAttrTypes.length),superAttrTypes,superStrSizes);
					int keyInt = temp.getIntFld(column);
					interBTF[i].insert(new IntegerKey(keyInt), rid1);
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

	private void createHeapFiles(){
		try {
			kResultsFile = new Heapfile("topKResults.in");
			interTAtuples = new Heapfile("interTATuples.in");

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
	}
	
	public void printKFile(){
		try{
			int attrCount = combinedAttrTypes.length;
			FldSpec[] tProjection = new FldSpec[attrCount];
			for (int i = 0; i < attrCount; i++)
				tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
			FileScan tempScan = new FileScan("topKResults.in",combinedAttrTypes,superStrSizes,(short)combinedAttrTypes.length,combinedAttrTypes.length,tProjection,null);
			Sort tempSortedFile = new Sort(combinedAttrTypes, (short)combinedAttrTypes.length, superStrSizes, tempScan, combinedAttrTypes.length, new TupleOrder(TupleOrder.Descending), 4, 12);
			Tuple tempTuple = new Tuple();
			System.out.println("k Results:");
			tempTuple = tempSortedFile.get_next();
			while(tempTuple!=null){
				tempTuple.setHdr((short)combinedAttrTypes.length, combinedAttrTypes, superStrSizes);
				tempTuple.print(combinedAttrTypes);
				tempTuple = tempSortedFile.get_next();
			}
			tempScan.closeFlag=true;
			tempScan.close();
			tempSortedFile.close();
		}
		catch(Exception e){
			System.out.println("Error in printKFile");
			e.printStackTrace();
		}
	}

	public void printTopKTuples(){
		try{
			min = numberOfTables;
			createHeapFiles();
			while(true)
			{
				//min = numberOfTables;
				performOneIteration();
				//System.out.println("Min: "+min);
				//System.out.println("threshold: "+threshold);
				if(min>=threshold && kResultsFile.getRecCnt()==knumberOfTuples)
					break;
			}
			printKFile();
		}
		catch(Exception e){
			System.out.println("Exception in printTopKTuples");
			e.printStackTrace();
		}
	}

	private boolean checkIfHighestOnesSatisfy(String key, AttrType attrType,int relNumber,Tuple mainTuple){
		try{
			if(duplFlag)
				return false;
			float minTemp = 0;


			attrTypes = new AttrType[proj_list.length];
			int strCount =0;
			for(int i=0;i<attrTypes.length;i++){
				attrTypes[i] = inputRelations[proj_list[i].relation.key][proj_list[i].offset-1];
				if(attrTypes[i].attrType==AttrType.attrString)
					strCount++;
			}
			tempStringSizes = new short[strCount];
			for(int i=0;i<strCount;i++){
				tempStringSizes[i]=30;
			}
			combinedTuple = new Tuple();
			//tupleCopy.setHdr((short)proj_list.length, attrTypes, tempStringSizes);
			combinedTuple.setHdr((short)combinedAttrTypes.length, combinedAttrTypes, superStrSizes);
			combinedTuple.setFloFld(combinedAttrTypes.length, 0);

			for(int rel=0;rel<numberOfTables;rel++){
				Tuple tempTuple=new Tuple();
				if(relNumber==rel){
					//System.out.println("In main tuple set Score..Setting : " + mainTuple.getScore());
					//combinedTuple.setScore(combinedTuple.getScore() + mainTuple.getScore());
					combinedTuple.setFloFld(combinedAttrTypes.length, mainTupleScore + combinedTuple.getFloFld(combinedAttrTypes.length));
					//System.out.println("Main Tuple is (in first if) : ");
					//mainTuple.print(mainTuple.attr_Types);

				}
				if(relNumber!=rel){
					int attrCount = inputRelations[rel].length+1;
					FldSpec[] tProjection = new FldSpec[attrCount];
					for (int i = 0; i < attrCount; i++)
						tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);

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
					int index;
					AttrType[] tempAttrTypes = new AttrType[inputRelations[rel].length+1];
					int strCounter = 0;
					for(index=0;index<tempAttrTypes.length-1;index++){
						tempAttrTypes[index] = inputRelations[rel][index];
						//System.out.println("Attribute Types : [" + index + "] " + tempAttrTypes[index]);
						if(tempAttrTypes[index].attrType==AttrType.attrString)
							strCounter++;
					}
					short[] tempStringSizes = new short[strCounter];
					for(index=0;index<strCounter;index++){
						tempStringSizes[index] = 30;
					}
					tempAttrTypes[tempAttrTypes.length-1] = new AttrType(AttrType.attrInteger);
					//System.out.println("Main Tuple : ");
					//mainTuple.print(mainTuple.attr_Types);
					/*System.out.println("index file Name: "+ indexFileNames[rel]);
					System.out.println("index Names: "+ indexNames[rel]);
					System.out.println("attrCount: "+ attrCount);*/
					//tempAttrTypes[index] = new AttrType(AttrType.attrReal);
					IndexScan tempIndex = new IndexScan(new IndexType(IndexType.B_Index), indexFileNames[rel], indexNames[rel], inputRelations[rel], stringSizes[rel], inputRelations[rel].length, inputRelations[rel].length, tProjection, expr, joinColumns[rel]+1, false);
					RID rid = new RID();
					tempTuple = tempIndex.get_next(rid);
					Tuple ridTuple = new Tuple();
					ridTuple.setHdr((short)tempAttrTypes.length, tempAttrTypes, tempStringSizes);
					rid = ConstantVars.getGlobalRID();
					for(int i=0;i<tempAttrTypes.length-1;i++){
						switch(tempAttrTypes[i].attrType){
						case AttrType.attrInteger:
							ridTuple.setIntFld(i+1,tempTuple.getIntFld(i+1));
							break;
						case AttrType.attrString:
							ridTuple.setStrFld(i+1,tempTuple.getStrFld(i+1));
							break;
						case AttrType.attrReal:
							ridTuple.setFloFld(i+1,tempTuple.getFloFld(i+1));
							break;
						}
					}
					ridTuple.setIntFld(tempAttrTypes.length, (rid.pageNo.pid*1000+rid.slotNo));
					//System.out.println("RID in index scan : " + rid.pageNo + ":" + rid.slotNo);
					int counter = 0;
					//System.out.println("Lets see if this works");
					//ridTuple.print(tempAttrTypes);
					Heapfile tempHeapfile = new Heapfile("tempResults.in");

					//System.out.println("Reading from index file");
					while(ridTuple!=null){
						//System.out.println("Printing ridTuple");
						//ridTuple.print(tempAttrTypes);
						//System.out.println(ridTuple.getIntFld(inputRelations[rel].length+1));
						if(counter>=knumberOfTuples)
							break;
						else{
							superTuple.setFloFld(superAttrTypes.length, mainTuple.getScore());
							//System.out.println("inserting the above record into heapfile");
							//System.out.println();
							RID tempTupleRID = ConstantVars.getGlobalRID();
							int RIDVal = tempTupleRID.pageNo.pid*1000 + tempTupleRID.slotNo;
							//System.out.println("RID Value is (in while) " + RIDVal);
							updateSuperTuple(superTuple,tempTuple,rel,RIDVal,false);
							//System.out.println("RIDs");
							java.util.Iterator iter = readRIDs.iterator();
							/*while(iter.hasNext()){
								System.out.print(iter.next() + "\t");
							}*/
							if(!readRIDs.contains(RIDVal)){
								//System.out.println("Inserting tuple");
								//ridTuple.print(tempAttrTypes);
								RID insertRID = tempHeapfile.insertRecord(ridTuple.getTupleByteArray());
								ridTuple = tempHeapfile.getRecord(insertRID);
								//ridTuple.print(tempAttrTypes);
								ridTuple.setHdr((short)tempAttrTypes.length, tempAttrTypes, stringSizes[rel]);
								//System.out.println("Tuple first field");
								//System.out.println(ridTuple.getStrFld(1));
								//System.out.println("Tuple second field");
								//System.out.println(ridTuple.getStrFld(2));
							}
							tempTuple = tempIndex.get_next(rid);
							if(tempTuple==null)
									break;
							rid = ConstantVars.getGlobalRID();
							for(int i=0;i<tempAttrTypes.length-1;i++){
								switch(tempAttrTypes[i].attrType){
								case AttrType.attrInteger:
									ridTuple.setIntFld(i+1,tempTuple.getIntFld(i+1));
									break;
								case AttrType.attrString:
									ridTuple.setStrFld(i+1,tempTuple.getStrFld(i+1));
									break;
								case AttrType.attrReal:
									ridTuple.setFloFld(i+1,tempTuple.getFloFld(i+1));
									break;
								}
							}
							ridTuple.setIntFld(tempAttrTypes.length, rid.pageNo.pid*1000+rid.slotNo);
							//System.out.println("RID in index scan : " + rid.pageNo + ":" + rid.slotNo);
							counter++;
						}	
					}
					//System.out.println("ridTuple out of while");
					//ridTuple.print(tempAttrTypes);
					
					//System.out.println("TempAttrType length" + tempAttrTypes.length);
					//System.out.println("Tproj length : " + tProjection.length);
					//System.out.println("Size of file: " + tempHeapfile.getRecCnt());
					//FileScan tempScan = new FileScan("tempResults.in", tempAttrTypes, stringSizes[rel],(short) tempAttrTypes.length, tempAttrTypes.length, tProjection, null);
					//FileScan tempScan = new FileScan("tempResults.in", tempAttrTypes, stringSizes[rel],(short) tempAttrTypes.length, tempAttrTypes.length, tProjection, null);
					FileScan tempScan = new FileScan("tempResults.in",tempAttrTypes,stringSizes[rel],(short)tempAttrTypes.length,tempAttrTypes.length,tProjection,null);
					//Scan tempoScan = new Scan(tempHeapfile);
					Tuple t1 = tempScan.get_next(rid);
					//System.out.println("File Scan Tuple: ");
					//t1.print(tempAttrTypes);
					Sort tempSortedFile = new Sort(tempAttrTypes, (short)tempAttrTypes.length, stringSizes[rel], tempScan, tempAttrTypes.length-1, new TupleOrder(TupleOrder.Descending), 4, 12);
					//System.out.println("Highest Tuple retrieved is : ");
					tempTuple = tempSortedFile.get_next();
					tempTuple.setHdr((short)tempAttrTypes.length, tempAttrTypes, stringSizes[rel]);
					//tempTuple.print(tempAttrTypes);
					tempSortedFile.close();
					tempHeapfile.deleteFile();
					tempIndex.closeFlag=true;
					tempIndex.close();
				}
				if(!duplFlag){
					for(int projIndex = 0;projIndex < combinedAttrTypes.length-1;projIndex++){
						//System.out.println("Projection Index : " + projIndex);
						if(tupleOffsets[rel]<=projIndex && tupleOffsets[rel+1]>projIndex && rel!=relNumber){
							//System.out.println("Came into first if part");
							switch(combinedAttrTypes[projIndex].attrType){
							case AttrType.attrInteger:
								//System.out.println("Setting value(int)" + tempTuple.getIntFld(projIndex-tupleOffsets[rel])+1);
								combinedTuple.setIntFld(projIndex+1,tempTuple.getIntFld(projIndex-tupleOffsets[rel]+1));
								break;
							case AttrType.attrString:
								//tempTuple.print(tempTuple.attr_Types);
								//System.out.println("Switch case : " + projIndex);
								//System.out.println("TempTuple : ");
								//tempTuple.print(tempTuple.attr_Types);
								//System.out.println("Combined Tuple : ");
								//combinedTuple.print(combinedTuple.attr_Types);
								//System.out.println("Setting value (str)" + tempTuple.getStrFld(projIndex-tupleOffsets[rel]+1));
								combinedTuple.setStrFld(projIndex+1,tempTuple.getStrFld(projIndex-tupleOffsets[rel]+1));
								break;
							case AttrType.attrReal:
								//System.out.println("Setting value (real)" + tempTuple.getFloFld(projIndex-tupleOffsets[rel]+1));
								combinedTuple.setFloFld(projIndex+1,tempTuple.getFloFld(projIndex-tupleOffsets[rel]+1));
								break;
							}
							//combinedTuple.setFloFld(combinedAttrTypes.length,tempTuple.getFloFld(inputRelations[rel].length)+combinedTuple.getFloFld(combinedAttrTypes.length));
						}
						else if(rel==relNumber && projIndex>=tupleOffsets[rel] && projIndex<tupleOffsets[rel+1]){
							switch(combinedAttrTypes[projIndex].attrType){
							case AttrType.attrInteger:
								//System.out.println("Setting value(main int): " + mainTuple.getIntFld(projIndex-tupleOffsets[rel]+1));
								combinedTuple.setIntFld(projIndex+1,mainTuple.getIntFld(projIndex-tupleOffsets[rel]+1));
								break;
							case AttrType.attrString:
								//System.out.println("Setting value(main str): " + mainTuple.getStrFld(projIndex-tupleOffsets[rel]+1));
								combinedTuple.setStrFld(projIndex+1,mainTuple.getStrFld(projIndex-tupleOffsets[rel]+1));
								break;
							case AttrType.attrReal:
								//System.out.println("Setting value(main flo): " + mainTuple.getFloFld(projIndex-tupleOffsets[rel]+1));
								combinedTuple.setFloFld(projIndex+1,mainTuple.getFloFld(projIndex-tupleOffsets[rel]+1));
								break;
							}
							//combinedTuple.setFloFld(combinedAttrTypes.length,mainTuple.getFloFld(inputRelations[rel].length)+combinedTuple.getFloFld(combinedAttrTypes.length));
						}
					}
					if(relNumber!=rel){
						//System.out.println("Trying to set score in if : TempTuple Score" + tempTuple.getScore());
						//System.out.println("Before update " + combinedTuple.getFloFld(combinedAttrTypes.length));
						combinedTuple.setFloFld(combinedAttrTypes.length,combinedTuple.getFloFld(combinedAttrTypes.length)+tempTuple.getFloFld(inputRelations[rel].length));
						//System.out.println("After update " + combinedTuple.getFloFld(combinedAttrTypes.length));
					}
				}
			}
			combinedTuple.setFloFld(combinedAttrTypes.length,combinedTuple.getFloFld(combinedAttrTypes.length)/numberOfTables);
			superTuple.setFloFld(superAttrTypes.length, superTuple.getFloFld(superAttrTypes.length)/numberOfTables);
			//System.out.println("Final Score: " + combinedTuple.getScore());
			//insertAndUpdateMin(kResultsFile,combinedTuple);
			System.out.println("FINAL TUPLE");
			combinedTuple.print(combinedAttrTypes);
			//System.out.println(combinedTuple.getFloFld(combinedAttrTypes.length));
			insertAndUpdateMin(kResultsFile, combinedTuple,0);
			interTAtuples.insertRecord(superTuple.getTupleByteArray());

			if(minTemp<min)
				return false;
			else
				return true;
		}
		catch(Exception e){
			System.out.println("Exception in checkIfHighestOnesSatisfy");
			e.printStackTrace();
		}
		return false;
	}

	private void updateSuperTuple(Tuple superTuple, Tuple otherTuple, int relNumber, int rid, boolean isMainRel){
		try{
			if(isMainRel){
				try{
					for(int i=0;i<otherTuple.attr_Types.length;i++){
						switch(otherTuple.attr_Types[i].attrType){
						case AttrType.attrInteger: 
							superTuple.setIntFld(superOffsets[relNumber]+i+1, otherTuple.getIntFld(i+1));
							break;
						case AttrType.attrString:
							//otherTuple.print(otherTuple.attr_Types);
							//System.out.println("Setting value : " + otherTuple.getStrFld(i+1));
							superTuple.setStrFld(superOffsets[relNumber]+i+1, otherTuple.getStrFld(i+1));
							break;
						case AttrType.attrReal:
							superTuple.setFloFld(superOffsets[relNumber]+i+1, otherTuple.getFloFld(i+1));
							break;
						}
					}
				}
				catch(Exception e){
					e.printStackTrace();
				}
			}
			else{
				try{
					for(int i=0;i<otherTuple.attr_Types.length;i++){
						switch(otherTuple.attr_Types[i].attrType){
						case AttrType.attrInteger:
							superTuple.setIntFld(superOffsets[relNumber]+i+1, otherTuple.getIntFld(i+1));
							break;

						case AttrType.attrString:
							//otherTuple.print(otherTuple.attr_Types);
							//System.out.println("Setting value : " + otherTuple.getStrFld(i+1));
							superTuple.setStrFld(superOffsets[relNumber]+i+1, otherTuple.getStrFld(i+1));
							break;
						case AttrType.attrReal:
							superTuple.setFloFld(superOffsets[relNumber]+i+1, otherTuple.getFloFld(i+1));
							break;
						}
					}
					superTuple.setIntFld(superOffsets[relNumber]+inputRelations[relNumber].length+1,rid);
					//System.out.println("After superTuple else update: ");

				}
				catch(Exception e){
					e.printStackTrace();
				}
			}
			superTuple.setFloFld(superTuple.attr_Types.length, superTuple.getFloFld(superTuple.attr_Types.length) + otherTuple.getScore());
//			superTuple.print(superAttrTypes);
		}
		catch(Exception e){
			e.printStackTrace();
		}
	}

	private void insertAndUpdateMin(Heapfile heapFile, Tuple tuple, int tupleFlag){
		try{
			//System.out.println("Before Min RID Page : " + minRID.pageNo + " Slot : " + minRID.slotNo);
			int recordCount=0;
			RID taRID, tempRID;
			tempRID = new RID();
			float tupScore = tuple.getFloFld(tuple.attr_Types.length);
			if(tupScore>min || kResultsFile.getRecCnt()<numberOfTables){
				tempRID = heapFile.insertRecord(tuple.getTupleByteArray());
			}
			if(heapFile.getRecCnt()>knumberOfTuples){
				heapFile.deleteRecord(minRID);
			}
			for(int i=0;i<numberOfTables;i++){
				kMinimums[i]=2.0f;
			}
			//System.out.println("\n\nCurrent Records");
			Scan fileScan = new Scan(heapFile);
			float tempMin=numberOfTables;
			taRID = new RID();
			Tuple tempTuple = fileScan.getNext(taRID);
			tupleCopy = new Tuple();
			if(tupleFlag==0){
			tupleCopy.setHdr((short)combinedAttrTypes.length,combinedAttrTypes,superStrSizes);
			//tupleCopy = new Tuple();
			tempTuple.setHdr((short)combinedAttrTypes.length,combinedAttrTypes,superStrSizes);
			}
			if(tupleFlag==1){
				tupleCopy.setHdr((short)superAttrTypes.length,superAttrTypes,superStrSizes);
				//tupleCopy = new Tuple();
				tempTuple.setHdr((short)superAttrTypes.length,superAttrTypes,superStrSizes);
			}
			boolean flag = false;
			int valRID = taRID.pageNo.pid*1000 + taRID.slotNo;
			tempMin = numberOfTables;
			//tempMin = tempTuple.getFloFld(combinedAttrTypes.length);
			while(tempTuple!=null){
				//System.out.println("Getting record from page: " + taRID.pageNo + " Slot: " + taRID.slotNo);
				tupleCopy.tupleCopy(tempTuple);
				//tempTuple.setHdr((short)combinedAttrTypes.length,combinedAttrTypes,superStrSizes);
				//System.out.println("Field number is : " + combinedAttrTypes.length);
				//System.out.println("Printing temptuple : ");
				//tempTuple.print(combinedAttrTypes);
				float score=0;
				for(int i=0;i<numberOfTables;i++){
					if(kMinimums[i]>tupleCopy.getFloFld(tupleOffsets[i+1]-1)){
						kMinimums[i]=tupleCopy.getFloFld(tupleOffsets[i+1]-1);
					}
				}
				
				//System.out.println("Tuple fld length" + tupleCopy.attr_Types.length);
				if(tupleFlag==0)
						score = tupleCopy.getFloFld(combinedAttrTypes.length);
				else
						score = tupleCopy.getFloFld(superAttrTypes.length);
				//float score = tupleCopy.getScore();
				//System.out.println("Tuple score is " + score + " and Minimum score is " + min + " and tempMin score is: " + tempMin);
				//tempTuple.print(tempTuple.attr_Types);
				//System.out.println(tupleCopy.getScore());
				//System.out.println();
				if(tempMin>=score ){
					tempMin = score;
					//System.out.println("Came into the if condition for score: " + score);
					if(minRID==null){
						//System.out.println("First visit into the function");
						minRID.pageNo = taRID.pageNo;
						minRID.slotNo = taRID.slotNo;
						break;
					}
					else{
						/*if(minRID!=null&& ((taRID.pageNo==minRID.pageNo && taRID.slotNo!=minRID.slotNo)
							|| (taRID.pageNo!=minRID.pageNo && taRID.slotNo==minRID.slotNo))
							||(taRID.pageNo!=minRID.pageNo && taRID.slotNo!=minRID.slotNo)){*/

						//System.out.println("Going into the second if");
						/*tempRID.pageNo = taRID.pageNo;
						tempRID.slotNo = taRID.slotNo;*/
						minRID.pageNo = taRID.pageNo;
						minRID.slotNo = taRID.slotNo;
						flag = true;
						//System.out.println("Temp Min now is " + tempMin);
						min=tempMin;
						//System.out.println("Min value now is " + min);
						//}
					}

				}
				tempTuple = fileScan.getNext(taRID);
				valRID = taRID.pageNo.pid * 1000 + taRID.slotNo;
				recordCount++;
			}
			
				/*minRID.pageNo = tempRID.pageNo;
				minRID.slotNo = tempRID.slotNo;
				System.out.println("After Min RID Page : " + minRID.pageNo + " Slot : " + minRID.slotNo);*/

		}
		catch(Exception e){
			System.out.println("Exception in insertAndUpdateMin");
			e.printStackTrace();
		}
	}

	private void performRandomAccess(String key,AttrType keyType,int relNumber,Tuple mainTuple){
		boolean firstOnesSatisfy = checkIfHighestOnesSatisfy(key,keyType,relNumber,mainTuple);
		int counter = 0;
		try{
			if(duplFlag){
				counter++;
				//System.out.println("Record Count (" + counter +"):" + kResultsFile.getRecCnt());
				//Tuple combinedTuple = new Tuple();
				attrTypes = new AttrType[proj_list.length+1];
				int strCount =0;
				for(int i=0;i<attrTypes.length-1;i++){
					attrTypes[i] = inputRelations[proj_list[i].relation.key][proj_list[i].offset-1];
					if(attrTypes[i].attrType==AttrType.attrString)
						strCount++;
				}
				attrTypes[attrTypes.length-1]=new AttrType(AttrType.attrInteger);

				tempStringSizes = new short[strCount];
				for(int i=0;i<tempStringSizes.length;i++)
					tempStringSizes[i]=30;

				/*combinedTuple = new Tuple();
				combinedTuple.setHdr((short)(superAttrTypes.length), superAttrTypes, superStrSizes);*/
				//updateSuperTuple(combinedTuple,mainTuple,relNumber,-1,true);
				//combinedTuple.setHdr((short)superAttrTypes.length, superAttrTypes, superStrSizes);
				//updateTuple(combinedTuple, mainTuple, relNumber);
				//updateSuperTuple(superTuple, mainTuple, relNumber, -1, true);
				combinedTuple.setScore(mainTuple.getScore());
				combinedTuple.setIntFld(combinedAttrTypes.length-1, 1);

				for(int i=0;i<numberOfTables;i++){
					if(relNumber!=i){
						checkForOthers(key,keyType,i,combinedTuple);
						mainRelNum = relNumber;
					}
				}
			}
		}
		catch(Exception e){
			System.out.println("Exception caught in performRandomAccess");
			e.printStackTrace();
		}
	}

	private void checkForOthers(String key, AttrType keyType, int relNum, Tuple tuple){
		try{
			if(relNum>=numberOfTables)
				return;
			int attrCount = inputRelations[relNum].length;
			FldSpec[] tProjection = new FldSpec[attrCount];
			for (int i = 0; i < attrCount; i++)
				tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);

			CondExpr[] expr = new CondExpr[2];
			expr[0] = new CondExpr();
			expr[0].op = new AttrOperator(AttrOperator.aopEQ);
			expr[0].type1 = new AttrType(AttrType.attrSymbol);
			expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), joinColumns[0]+1);
			if(keyType.attrType==AttrType.attrInteger){
				expr[0].type2 = new AttrType(AttrType.attrInteger);
				expr[0].operand2.integer = Integer.parseInt(key);
			}
			else{
				expr[0].type2 = new AttrType(AttrType.attrString);
				expr[0].operand2.string= key;
			}			
			expr[0].next = null;
			expr[1] = null;

			IndexScan tempIndex = new IndexScan(new IndexType(IndexType.B_Index), indexFileNames[relNum], indexNames[relNum], inputRelations[relNum], stringSizes[relNum], attrCount, attrCount, tProjection, expr, joinColumns[relNum]+1, false);
			Tuple simpleTuple = new Tuple();
			int counter = 0,strCount=0;
			for(int i=0;i<attrTypes.length-1;i++){
				attrTypes[i] = inputRelations[proj_list[i].relation.key][proj_list[i].offset-1];
				if(attrTypes[i].attrType==AttrType.attrString)
					strCount++;
			}
			short[] tempStringSizes = new short[strCount];
			for(int i=0;i<strCount;i++){
				tempStringSizes[i]=30;
			}
			boolean firstTime = true;
			float tupleScore = tuple.getFloFld(combinedAttrTypes.length);
			RID rid = new RID();
			float superScore = superTuple.getFloFld(superAttrTypes.length);
			while((simpleTuple=tempIndex.get_next(rid))!=null){
				tuple.setFloFld(combinedAttrTypes.length, mainTupleScore);
				superTuple.setFloFld(superAttrTypes.length, mainTupleScore);
				counter++;
				rid = ConstantVars.getGlobalRID();
				if(readRIDs.contains(rid.pageNo.pid*1000+rid.slotNo))
					continue;
				//tuple.setScore(tupleScore);
				//System.out.println("Tuple in checkOthers : ");
				//tuple.print(tuple.attr_Types);
				//System.out.println("Simple Tuple is");
				//simpleTuple.print(simpleTuple.attr_Types);
				//updateTuple(tuple,simpleTuple,relNum);
				updateSuperTuple(tuple,simpleTuple,relNum,rid.pageNo.pid*1000+rid.slotNo,false);
				updateSuperTuple(superTuple,simpleTuple,relNum,rid.pageNo.pid*1000+rid.slotNo,false);
				//superTuple.print(superAttrTypes);
				tuple.setFloFld(combinedAttrTypes.length,(tupleScore + simpleTuple.getScore()));
				if(firstTime){
					tuple.setIntFld(combinedAttrTypes.length-1, tuple.getIntFld(combinedAttrTypes.length-1)+1);
					firstTime = false;
				}
				//System.out.println("After updateTuple");
				tuple.print(combinedAttrTypes);
				if(numberOfTables==tuple.getIntFld(combinedAttrTypes.length-1)){
					tupleCopy.setHdr((short)(proj_list.length+1), attrTypes, tempStringSizes);
					tuple.setFloFld(combinedAttrTypes.length,tuple.getFloFld(combinedAttrTypes.length)/numberOfTables);
					//insertAndUpdateMin(kResultsFile, tuple);
					superTuple.setFloFld(superAttrTypes.length, superScore + simpleTuple.getScore());
					superTuple.setFloFld(superAttrTypes.length, superTuple.getFloFld(superAttrTypes.length)/numberOfTables);
					superTuple.setScore(superTuple.getFloFld(superAttrTypes.length));
					insertAndUpdateMin(kResultsFile,tuple,0);
					RID insertRID = interTAtuples.insertRecord(superTuple.getTupleByteArray());
					//superTuple.print(superAttrTypes);
					//System.out.println("Inserted at position " + insertRID.pageNo + ":" + insertRID.slotNo);
				}
				else if(relNum==numberOfTables && relNum!=mainRelNum){
					checkForOthers(key, keyType, 1, tuple);
					tuple.setIntFld(combinedAttrTypes.length-1, tuple.getIntFld(combinedAttrTypes.length-1)+1);
				}
				else if(relNum!=mainRelNum){
					checkForOthers(key, keyType, relNum + 1, tuple);
					tuple.setIntFld(combinedAttrTypes.length-1, tuple.getIntFld(combinedAttrTypes.length-1)+1);
				}
				else{
					//System.out.println("Do Nothing");
				}
			}
			return;
		}
		catch(Exception e){
			System.out.println("Exception in checkForOthers");
			e.printStackTrace();
		}
	}

	private void updateTuple(Tuple mainTuple, Tuple subTuple, int relNumber){
		try{
			int diff = tupleOffsets[relNumber]-1;
			for(int i=tupleOffsets[relNumber];i<tupleOffsets[relNumber+1];i++){
				//System.out.println("Index to find: " + (i-diff));
				switch(superAttrTypes[i].attrType){
				case AttrType.attrInteger:
					//System.out.println("Value setting(int): " + subTuple.getIntFld(i-diff));
					mainTuple.setIntFld(i+1, subTuple.getIntFld(i-diff));
					break;
				case AttrType.attrString:
					//System.out.println("Value setting(str): " + subTuple.getStrFld(i-diff));
					mainTuple.setStrFld(i+1, subTuple.getStrFld(i-diff));
					break;
				case AttrType.attrReal:
					//System.out.println("Value setting(real): " + subTuple.getFloFld(i-diff));
					mainTuple.setFloFld(i+1, subTuple.getFloFld(i-diff));
					break;
				}
			}
		}
		catch(Exception e){
			System.out.println("Exception in updateTuple");
			e.printStackTrace();
		}
	}

	private void performOneIteration(){
		float thresholdTemp = 0;
		for(int relNumber=0;relNumber<numberOfTables;relNumber++){
			try{
				//System.out.println("Completed one iteration");
				//System.out.println("===========================================================");

				//System.out.println("");
				//System.out.println("===========================================================");
				Tuple mainTuple = iterators[relNumber].get_next();
				//RID tempRID = ConstantVars.getGlobalRID();
				//System.out.println("Main Tuple is ");
				//mainTuple.print(inputRelations[relNumber]);
				//System.out.println("Main Tuple in performOneIter ");
				//System.out.println(mainTuple.getScore());
				mainTupleScore = mainTuple.getScore();
				mainTuple.setFloFld(inputRelations[relNumber].length,mainTuple.getScore());
				superTuple = new Tuple();
				superTuple.setHdr((short)superAttrTypes.length, superAttrTypes, superStrSizes);
				updateSuperTuple(superTuple,mainTuple,relNumber,-1,true);
				combinedTuple = new Tuple();
				combinedTuple.setHdr((short)combinedAttrTypes.length,combinedAttrTypes,superStrSizes);
				updateSuperTuple(combinedTuple,mainTuple,relNumber,-1,true);
				int RIDNum = mainTuple.getIntFld(inputRelations[relNumber].length+1);
				//System.out.println("Main Tuple RID : " + RIDNum);
				readRIDs.add(RIDNum);
				//java.util.Iterator<Integer> iter = readRIDs.iterator();
				/*while(iter.hasNext()){
					System.out.print(iter.next()+"\t");
				}*/
				//System.out.println();
				AttrType keyType = inputRelations[relNumber][joinColumns[relNumber]];
				if(!duplFlag){
					switch(keyType.attrType){
					case AttrType.attrInteger:
						if(readIntKeys.contains(mainTuple.getIntFld(joinColumns[relNumber]+1)))
							continue;
						else
							readIntKeys.add(mainTuple.getIntFld(joinColumns[relNumber]+1));
						break;
					case AttrType.attrString:
						if(readStrKeys.contains(mainTuple.getStrFld(joinColumns[relNumber]+1)))
							continue;
						else
							readStrKeys.add(mainTuple.getStrFld(joinColumns[relNumber]+1));
						break;

					}
				}
				switch(keyType.attrType){
				case AttrType.attrInteger:
					int intKey = mainTuple.getIntFld(joinColumns[relNumber]+1);
					performRandomAccess(String.valueOf(intKey),keyType,relNumber,mainTuple);
					break;
				case AttrType.attrString:
					String strKey = mainTuple.getStrFld(joinColumns[relNumber]+1);
					performRandomAccess(strKey,keyType,relNumber,mainTuple);
					break;
				}
				thresholdTemp += mainTuple.getScore();
			}
			catch(Exception e){
				System.out.println("Caught exception in performOneIteration");
				e.printStackTrace();
			}
		}
		threshold=thresholdTemp/numberOfTables;
	}	

	public void updateTAResults(Iterator[] additions, Iterator[] del){
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
				int attrCount = inputRelations[relation].length+1;
				FldSpec[] tProjection = new FldSpec[attrCount];
				for (int i = 0; i < attrCount; i++)
					tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);

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

				IndexScan tempIndex = new IndexScan(new IndexType(IndexType.B_Index), indexFileNames[relation], indexNames[relation], inputRelations[relation], stringSizes[relation], inputRelations[relation].length, inputRelations[relation].length, tProjection, expr, joinColumns[relation]+1, false);
				Tuple tempTuple = tempIndex.get_next();
				RID temprid=new RID();
				while(tempTuple!=null){
					temprid = ConstantVars.getGlobalRID();
					if(tuplesMatch(tuple,tempTuple,inputRelations[relation]))
						break;
					tempTuple = tempIndex.get_next();
				}
				if(tempTuple!=null){
					if(kMinimums[relation]<tempTuple.getFloFld(inputRelations[relation].length)){
						deleteFromKTuples(relation,temprid);
						System.out.println("Deletion should happen for record in relation " + relation + " with score " + tempTuple.getFloFld(inputRelations[relation].length));
					}
					deleteFromInterFile(temprid,relation);
				}
			}
			if(kResultsFile.getRecCnt() < knumberOfTuples)
				insertRemainingTuples();
			printKFile();
		}
		catch(Exception e){
			System.out.println("Error in deleteTuple");
			e.printStackTrace();
		}
	}
	
	private void insertRemainingTuples(){
		try{
			int attrCount = superAttrTypes.length;
			FldSpec[] tProjection = new FldSpec[attrCount];
			for (int i = 0; i < attrCount; i++)
				tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
			FileScan tempScan = new FileScan("interTATuples.in",superAttrTypes,superStrSizes,(short)superAttrTypes.length,superAttrTypes.length,tProjection,null);
			Sort tempSortedFile = new Sort(superAttrTypes, (short)superAttrTypes.length, superStrSizes, tempScan, superAttrTypes.length, new TupleOrder(TupleOrder.Descending), 4, 12);
			Tuple tempTuple = new Tuple();
			tempTuple = tempSortedFile.get_next();
			Tuple kTuple = new Tuple();
			kTuple.setHdr((short)combinedAttrTypes.length,combinedAttrTypes,superStrSizes);
			int counter=0;
			while(kResultsFile.getRecCnt()<knumberOfTuples){
				tempTuple.setHdr((short)superAttrTypes.length,superAttrTypes,superStrSizes);
				for(int i=1;i<=combinedAttrTypes.length-2;i++){
					switch(combinedAttrTypes[i-1].attrType){
					case AttrType.attrInteger:
						kTuple.setIntFld(i, tempTuple.getIntFld(i));
						break;
					case AttrType.attrString:
						kTuple.setStrFld(i,tempTuple.getStrFld(i));
						break;
					case AttrType.attrReal:
						kTuple.setFloFld(i, tempTuple.getFloFld(i));
						break;
					}
				}
				kTuple.setFloFld(combinedAttrTypes.length, tempTuple.getFloFld(superAttrTypes.length));
				checkAndInsert(kTuple);
				tempTuple = tempSortedFile.get_next();
				
			}
		}
		catch(Exception e){
			System.out.println("Exception in insertRemainingTuples");
			e.printStackTrace();
		}
	}
	
	public void checkAndInsert(Tuple kTuple){
		try{
			Scan scan = new Scan(kResultsFile);
			Tuple tempTuple = new Tuple();
			tempTuple.setHdr((short)combinedAttrTypes.length, combinedAttrTypes, superStrSizes);
			RID rid = new RID();
			tempTuple = scan.getNext(rid);
			int count = 0;
			while(tempTuple!=null){
				tempTuple.setHdr((short)combinedAttrTypes.length, combinedAttrTypes, superStrSizes);
				boolean smallFlag = true;
				for(int i=0;i<numberOfTables;i++){
					if(tempTuple.getIntFld(tupleOffsets[i+1])!=kTuple.getIntFld(tupleOffsets[i+1])){
						smallFlag = false;
					}
				}
				if(!smallFlag){
					count++;
				}
				tempTuple = scan.getNext(rid);
			}
			if(count==kResultsFile.getRecCnt()){
				kResultsFile.insertRecord(kTuple.getTupleByteArray());
			}
		}
		catch(Exception e){
			System.out.println("Exception in checkAndInsert");
			e.printStackTrace();
		}
	}
	
	private void deleteFromKTuples(int relation,RID temprid){
		try{
			int RIDVal = temprid.pageNo.pid*1000 + temprid.slotNo;
			Scan fs = new Scan(kResultsFile);
			RID rid = new RID();
			Tuple delTuple = fs.getNext(rid);
			while(delTuple!=null){
				delTuple.setHdr((short)combinedAttrTypes.length, combinedAttrTypes, superStrSizes);
				if(delTuple.getIntFld(tupleOffsets[relation+1])==RIDVal){
					kResultsFile.deleteRecord(rid);
				}
				delTuple = fs.getNext(rid);
			}
		}
		catch(Exception e){
			System.out.println("Exception in deleteFromKTuples");
			e.printStackTrace();
		}
	}

	private void deleteFromInterFile(RID delRID, int relation){
		try{
			System.out.println("Before delete " + interTAtuples.getRecCnt());
			int rid = delRID.pageNo.pid*1000 + delRID.slotNo;
			int colNum = superOffsets[relation] + inputRelations[relation].length;
			System.out.println("Index scan on the colNum " + colNum + " on RID : " + rid);
			int attrCount = superAttrTypes.length+1;
			FldSpec[] tProjection = new FldSpec[attrCount];
			for (int i = 0; i < attrCount; i++)
				tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);

			CondExpr[] expr = new CondExpr[2];
			expr[0] = new CondExpr();
			expr[0].op = new AttrOperator(AttrOperator.aopEQ);
			expr[0].type1 = new AttrType(AttrType.attrSymbol);
			expr[0].operand1.symbol = new FldSpec(new RelSpec(RelSpec.outer), colNum+1);
			expr[0].type2 = new AttrType(AttrType.attrInteger);
			expr[0].operand2.integer = rid;			
			expr[0].next = null;
			expr[1] = null;

			/*Scan s = new Scan(interTAtuples);
			Tuple t = new Tuple();
			t.setHdr((short)superAttrTypes.length, superAttrTypes,superStrSizes);
			RID srid = new RID();
			while((t=s.getNext(srid))!=null){
				t.print(superAttrTypes);
			}*/

			IndexScan interIndexScan = new IndexScan(new IndexType(IndexType.B_Index),"interTATuples.in",interIndexName[relation],superAttrTypes,superStrSizes,superAttrTypes.length,superAttrTypes.length,tProjection,expr,colNum+1,false);
			Tuple delTuple = interIndexScan.get_next();
			while(delTuple!=null){
				RID tempRID = ConstantVars.getGlobalRID();
				interTAtuples.deleteRecord(tempRID);
				delTuple = interIndexScan.get_next();
			}
			System.out.println("After delete " + interTAtuples.getRecCnt());
		}
		catch(Exception e){
			System.out.println("Error in deleteFromInterFile");
			e.printStackTrace();
		}
	}

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
}