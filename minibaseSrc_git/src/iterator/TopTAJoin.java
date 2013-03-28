package iterator;

import global.AttrOperator;
import global.AttrType;
import global.IndexType;
import global.RID;
import heap.HFBufMgrException;
import heap.HFDiskMgrException;
import heap.HFException;
import heap.Heapfile;
import heap.Scan;
import heap.Tuple;
import index.IndexScan;

import java.io.IOException;


public class TopTAJoin {
	private int numberOfTables;
	private AttrType inputRelations[][];
	private int lengths[];
	private short[][] stringSizes;
	private int joinColumns[];
	private Iterator iterators[];
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
	private Heapfile kResultsFile;
	private AttrType[] attrTypes;
	private int[] tupleOffsets;
	private int mainRelNum;
	private Tuple combinedTuple = new Tuple();
	private Tuple tupleCopy = new Tuple();
	Tuple finalTuple = new Tuple();

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
		tupleOffsets = new int[numTables];
		minRID = new RID();
		this.indexNames = new String[indexNames.length];

		//Setting minimum to number of Relations as it is max possible value
		threshold = numTables;
		
		for(int i=0;i<fileNames.length;i++){
			indexFileNames[i] = fileNames[i];
		}
		
		for(int i=0;i<indexNames.length;i++){
			this.indexNames[i] = indexNames[i];
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

		int count = 0;
		int prevRel = 0;
		for(int i=0;i<proj_list.length;i++){
			this.proj_list[i] = proj_list[i];
			if(prevRel!=this.proj_list[i].relation.key){
				tupleOffsets[prevRel] = count;
				count = 0;
				prevRel = this.proj_list[i].relation.key;
			}
		}
		}
		catch(Exception e){
			System.out.println("Exception in constructor");
			e.printStackTrace();
		}
		
	}

	private void createHeapFiles(){
		try {
			kResultsFile = new Heapfile("topKResults.in");
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

	public void printTopKTuples(){
		try{
			createHeapFiles();
			while(true)
			{
				performOneIteration();
				System.out.println("Min: "+min);
				System.out.println("threshold: "+threshold);
				if(min>=threshold)
					break;
			}
			Scan finalScan = new Scan(kResultsFile);
			
			Tuple t = new Tuple();
			RID rid = new RID();
			t = finalScan.getNext(rid);
			while(t!=null){
				finalTuple.tupleCopy(t);
				finalTuple.print(attrTypes);
				System.out.print(finalTuple.getScore());
				System.out.println();
				t = finalScan.getNext(rid);
			}
		}
		catch(Exception e){
			System.out.println("Exception in printTopKTuples");
			e.printStackTrace();
		}
	}

	private boolean checkIfHighestOnesSatisfy(String key, AttrType attrType,int relNumber,Tuple mainTuple){
		try{
			float minTemp = 0;
			
			attrTypes = new AttrType[proj_list.length];
			int strCount =0;
			for(int i=0;i<attrTypes.length;i++){
				attrTypes[i] = inputRelations[proj_list[i].relation.key][proj_list[i].offset];
				if(attrTypes[i].attrType==AttrType.attrString)
					strCount++;
			}
			short[] tempStringSizes = new short[strCount];
			for(int i=0;i<strCount;i++){
				tempStringSizes[i]=30;
			}
			tupleCopy.setHdr((short)proj_list.length, attrTypes, tempStringSizes);
			finalTuple.setHdr((short)proj_list.length, attrTypes, tempStringSizes);
			combinedTuple.setHdr((short)proj_list.length, attrTypes, tempStringSizes);
			for(int rel=0;rel<numberOfTables;rel++){
				Tuple tempTuple=new Tuple();
				if(relNumber==rel){
					System.out.println("In main tuple set Score..Setting : " + mainTuple.getScore());
					combinedTuple.setScore(mainTuple.getScore());
				}
				if(relNumber!=rel){
					int attrCount = inputRelations[rel].length;
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
					}			
					expr[0].next = null;
					expr[1] = null;
					IndexScan tempIndex = new IndexScan(new IndexType(IndexType.B_Index), indexFileNames[rel], indexNames[rel], inputRelations[rel], stringSizes[rel], attrCount, attrCount, tProjection, expr, joinColumns[rel]+1, false);
					//tempTuple = tempIndex.get_next();
					tempTuple=tempIndex.get_next();
					System.out.println("Score 1st: " + tempTuple.getScore());
					tempTuple=tempIndex.get_next();
					System.out.println("Score 2nd: " + tempTuple.getScore());
					tempTuple=tempIndex.get_next();
					System.out.println("Score 3rd: " + tempTuple.getScore());
					tempTuple=tempIndex.get_next();
					System.out.println("Score 4th: " + tempTuple.getScore());
					tempTuple=tempIndex.get_next();
					System.out.println("Score 5th: " + tempTuple.getScore());
					minTemp += tempTuple.getScore();
					tempIndex.close();
				}
				if(!duplFlag){
					
					for(int projIndex = 0;projIndex < proj_list.length;projIndex++){
						if(rel==proj_list[projIndex].relation.key && rel!=relNumber){
							switch(attrTypes[projIndex].attrType){
							case AttrType.attrInteger:
								combinedTuple.setIntFld(projIndex+1,tempTuple.getIntFld(proj_list[projIndex].offset));
								break;
							case AttrType.attrString:
								combinedTuple.setStrFld(projIndex+1, tempTuple.getStrFld(proj_list[projIndex].offset));
								break;
							case AttrType.attrReal:
								combinedTuple.setFloFld(projIndex+1, tempTuple.getFloFld(proj_list[projIndex].offset));
								break;
							}
							//combinedTuple.setScore(tempTuple.getScore()+combinedTuple.getScore());
						}
						else if(rel==relNumber && rel==proj_list[projIndex].relation.key){
							switch(attrTypes[projIndex].attrType){
							case AttrType.attrInteger:
								combinedTuple.setIntFld(projIndex+1,mainTuple.getIntFld(proj_list[projIndex].offset));
								break;
							case AttrType.attrString:
								combinedTuple.setStrFld(projIndex+1,mainTuple.getStrFld(proj_list[projIndex].offset));
								break;
							case AttrType.attrReal:
								combinedTuple.setFloFld(projIndex+1,mainTuple.getFloFld(proj_list[projIndex].offset));
								break;
							}
							//combinedTuple.setScore(mainTuple.getScore()+combinedTuple.getScore());
						}
					}
					if(relNumber!=rel){
						System.out.println("Trying to set score in if : TempTuple Score" + tempTuple.getScore());
						System.out.println("Before update " + combinedTuple.getScore());
					combinedTuple.setScore(tempTuple.getScore()+combinedTuple.getScore());
					System.out.println("After update " + combinedTuple.getScore());
					}
				}
			}
			combinedTuple.setScore(combinedTuple.getScore()/numberOfTables);
			System.out.println("Final Score: " + combinedTuple.getScore());
				insertAndUpdateMin(kResultsFile,combinedTuple);
		
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
	
	private void insertAndUpdateMin(Heapfile heapFile, Tuple tuple){
		try{
			int recordCount=0;
			RID taRID, tempRID;
			tempRID = new RID();
			tempRID = heapFile.insertRecord(tuple.getTupleByteArray());
			System.out.println("Record Count: "+heapFile.getRecCnt());
			Scan fileScan = new Scan(heapFile);
			float tempMin=numberOfTables;
			taRID = new RID();
			Tuple tempTuple = fileScan.getNext(taRID);
			while(tempTuple!=null){
				tupleCopy.tupleCopy(tempTuple);
				float score = tupleCopy.getScore();
				tupleCopy.print(tupleCopy.attr_Types);
				System.out.println(tupleCopy.getScore());
				System.out.println();
				if(tempMin>=score){
					tempMin = score;
					if(minRID!=null&&taRID.pageNo!=minRID.pageNo && taRID.slotNo!=minRID.slotNo){
					tempRID.pageNo = taRID.pageNo;
					tempRID.slotNo = taRID.slotNo;
					}
				}
				tempTuple = fileScan.getNext(taRID);
				recordCount++;
			}
			if(heapFile.getRecCnt()>knumberOfTuples)
				heapFile.deleteRecord(minRID);
			min=tempMin;
			minRID.pageNo = tempRID.pageNo;
			minRID.slotNo = tempRID.slotNo;
		}
		catch(Exception e){
			System.out.println("Exception in insertAndUpdateMin");
			e.printStackTrace();
		}
	}
	
	private void performRandomAccess(String key,AttrType keyType,int relNumber,Tuple mainTuple){
		boolean firstOnesSatisfy = checkIfHighestOnesSatisfy(key,keyType,relNumber,mainTuple);
		try{
			if(firstOnesSatisfy && duplFlag){
				Tuple combinedTuple = new Tuple();
				attrTypes = new AttrType[proj_list.length];
				int strCount =0;
				for(int i=0;i<attrTypes.length;i++){
					attrTypes[i] = inputRelations[proj_list[i].relation.key][proj_list[i].offset];
					if(attrTypes[i].attrType==AttrType.attrString)
						strCount++;
				}

				short[] tempStringSizes = new short[strCount];
				for(int i=0;i<stringSizes.length;i++)
					tempStringSizes[i]=30;

				combinedTuple.setHdr((short)proj_list.length, attrTypes, tempStringSizes);

				for(int i=0;i<numberOfTables;i++){
					if(relNumber!=i){
						checkForOthers(key,keyType,relNumber,combinedTuple);
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
			int attrCount = inputRelations[relNum+1].length;
			FldSpec[] tProjection = new FldSpec[attrCount];
			for (int i = 0; i < attrCount; i++)
				tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);

			CondExpr[] expr = new CondExpr[1];
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

			IndexScan tempIndex = new IndexScan(new IndexType(IndexType.B_Index), indexFileNames[relNum+1], indexNames[relNum+1], inputRelations[relNum+1], stringSizes[relNum+1], attrCount, attrCount, tProjection, expr, joinColumns[relNum+1]+1, false);
			Tuple simpleTuple = new Tuple();
			while((simpleTuple=tempIndex.get_next())!=null){
				updateTuple(tuple,simpleTuple,relNum+1);
				if(relNum==numberOfTables && relNum!=mainRelNum)
					checkForOthers(key, keyType, 1, tuple);
				else if(relNum!=mainRelNum)
					checkForOthers(key, keyType, relNum + 1, tuple);
				else
				{
					insertAndUpdateMin(kResultsFile, tuple);
				}
			}
		}
		catch(Exception e){
			System.out.println("Exception in checkForOthers");
		}
	}
	
	private void updateTuple(Tuple mainTuple, Tuple subTuple, int relNumber){
		try{
			for(int i=tupleOffsets[relNumber];i<tupleOffsets[relNumber+1];i++){
				switch(attrTypes[i].attrType){
				case AttrType.attrInteger:
					mainTuple.setIntFld(i, subTuple.getIntFld(proj_list[i].offset));
					break;
				case AttrType.attrString:
					mainTuple.setStrFld(i, subTuple.getStrFld(proj_list[i].offset));
					break;
				case AttrType.attrReal:
					mainTuple.setFloFld(i, subTuple.getFloFld(proj_list[i].offset));
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
				Tuple mainTuple = iterators[relNumber].get_next();
				AttrType keyType = inputRelations[relNumber][joinColumns[relNumber]];
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
}