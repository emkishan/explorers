package iterator;
import index.IndexException;
import index.IndexScan;
import java.io.IOException;
import java.util.HashMap;
import btree.AddFileEntryException;
import btree.BTreeFile;
import btree.ConstructPageException;
import btree.GetFileEntryException;
import btree.IntegerKey;
import btree.StringKey;
import bufmgr.HashEntryNotFoundException;
import bufmgr.InvalidFrameNumberException;
import bufmgr.PageNotReadException;
import bufmgr.PageUnpinnedException;
import bufmgr.ReplacerException;
import global.AttrOperator;
import global.AttrType;
import global.ConstantVars;
import global.IndexType;
import global.PageId;
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

public class StreamCombine {
	private int numTables;
	private AttrType[][] inputRelations;
	private boolean firstTime;
	private int[] lengths;
	private short[][] stringSizes;
	private int[] joinColumns;
	private Iterator[] iterators;
	private int no_buf_pgs;
	private CondExpr[] outFilter;
	private FldSpec[] proj_list;
	private int numOutFlds;
	private Tuple JTuple;
	private int numOutputFlds;
	private int knumTuples;
	private Heapfile kResultsFile;
	private int combinedAttrCount = 0;
	private Heapfile tempFile = null;
	private FileScan fScan = null;
	private Tuple mainTuple = new Tuple();
	private AttrType[] combinedAttr = null;
	private short[] combinedStrSizes = null;
	private FldSpec[] combinedProjection = null;
	private Tuple combinedTuple = new Tuple();
	private Tuple t = new Tuple();
	private int counter;
	private int kCounter;
	private int[] M;
	private float[] indicators;
	private int roundRobin =0;
	private float minScores[];
	int arr[] = null;
	BTreeFile btf1 = null;
	private boolean flag = false;
	private float[] kMinimums = null;
	public StreamCombine(int numTables, AttrType[][] in, int[] len_in,
			short[][] s_sizes, int[] join_col_in, Iterator[] am,
			int amt_of_mem, CondExpr[] outFilter, FldSpec[] proj_list,
			int n_out_flds, int num, int rr) {
		try {
			createHeapFiles();
			minScores = new float[numTables];
			kMinimums = new float[numTables];
			for(int i=0;i<numTables;i++)
			{
				minScores[i] =2;
				kMinimums[i]=2;
			}
			this.numTables = numTables;
			inputRelations = new AttrType[numTables][];
			joinColumns = new int[numTables];
			// Join Columns
			for (int i = 0; i < numTables; i++)
				joinColumns[i] = join_col_in[i];
			// Attribute Types
			lengths = new int[numTables];
			for (int i = 0; i < in.length; i++) {
				inputRelations[i] = new AttrType[in[i].length];
				lengths[i] = len_in[i];
				for (int j = 0; j < in[i].length; j++) {
					inputRelations[i][j] = in[i][j];
				}
			}
			// iterators
			iterators = new Iterator[am.length];
			for (int i = 0; i < numTables; i++) {
				iterators[i] = am[i];
			}
			// Copy the String sizes and initialize tuples
			stringSizes = new short[s_sizes.length][];
			for (int i = 0; i < numTables; i++) {
				stringSizes[i] = s_sizes[i];

			}
			firstTime = true;
			JTuple = new Tuple();
			no_buf_pgs = amt_of_mem;
			numOutputFlds = n_out_flds;
			knumTuples = num;
			kCounter = num;
			roundRobin = rr;
			M = new int[numTables];
			indicators = new float[numTables];
			this.outFilter = new CondExpr[outFilter.length];
			for (int i = 0; i < outFilter.length; i++) {
				this.outFilter[i] = outFilter[i];
			}
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
			combinedAttr[attrCount++] = new AttrType(AttrType.attrInteger);
			combinedAttr[attrCount++] = new AttrType(AttrType.attrReal);
			if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrInteger) {
				combinedAttr[attrCount++] = new AttrType(AttrType.attrInteger);
			} else if (inputRelations[0][joinColumns[0]].attrType == AttrType.attrString) {
				combinedAttr[attrCount++] = new AttrType(AttrType.attrString);
				combinedStrSizes[strCount++] = 20;
			}
			combinedProjection = new FldSpec[combinedAttrCount];
			for (int attr = 0; attr < combinedAttrCount; attr++) {
				combinedProjection[attr] = new FldSpec(new RelSpec(
						RelSpec.outer), attr + 1);
			}
			arr= new int[numTables];
			try {
				combinedTuple.setHdr((short) combinedAttrCount, combinedAttr,
						combinedStrSizes);
				mainTuple.setHdr((short) combinedAttrCount, combinedAttr,
						combinedStrSizes);
			} catch (InvalidTypeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InvalidTupleSizeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} catch (Exception ex) {
			ex.printStackTrace();
		}
	}	
	/*public void deleteTuple(Iterator iter,int relation){
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

				IndexScan tempIndex  = new IndexScan(new IndexType(IndexType.B_Index),
						"topKResults.in", "KTreeIndex", combinedAttr,
						combinedStrSizes, combinedAttrCount, combinedAttrCount,
						combinedProjection, expr, combinedAttrCount-1, false);
				Tuple tempTuple = tempIndex.get_next();
				RID temprid=new RID();
				while(tempTuple!=null){
					temprid = ConstantVars.getGlobalRID();
					if(tuplesMatch(tuple,tempTuple,inputRelations[relation]))
						break;
					tempTuple = tempIndex.get_next();
				}
				if(tempTuple!=null){
					temprid = ConstantVars.getGlobalRID();
					if(kMinimums[relation]<tempTuple.getFloFld(inputRelations[relation].length)){
						kResultsFile.deleteRecord(temprid);
						//System.out.println("Deletion should happen for record in relation " + relation + " with score " + tempTuple.getFloFld(inputRelations[relation].length));
					}
					deleteFromInterFile(temprid,relation);
				}
			}
			if(kResultsFile.getRecCnt() < knumTuples)
				insertRemainingTuples();
			printResults();
		}
		catch(Exception e){
			System.out.println("Error in deleteTuple");
			e.printStackTrace();
		}
	}
	private void insertRemainingTuples(){
		try{
			int attrCount = combinedAttr.length;
			FldSpec[] tProjection = new FldSpec[attrCount];
			for (int i = 0; i < attrCount; i++)
				tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
			FileScan tempScan = new FileScan("TempResults.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
			Sort tempSortedFile = new Sort(combinedAttr,
					(short) combinedAttrCount, combinedStrSizes, tempScan,
					combinedAttrCount-1, new TupleOrder(TupleOrder.Descending), 4, 20);
			Tuple tempTuple = new Tuple();
			tempTuple = tempSortedFile.get_next();
			Tuple kTuple = new Tuple();
			kTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
			int counter=0;
			while(kResultsFile.getRecCnt()<knumTuples){
				tempTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
				//System.out.println("Record from interFile");
				//tempTuple.print(superAttrTypes);
				for(int i=1;i<=combinedAttr.length-2;i++){
					switch(combinedAttr[i-1].attrType){
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
				kTuple.setFloFld(combinedAttr.length-1, tempTuple.getFloFld(combinedAttr.length-1));
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
			tempTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
			RID rid = new RID();
			tempTuple = scan.getNext(rid);
			int count = 0;
			while(tempTuple!=null){
				tempTuple.setHdr((short)combinedAttrCount, combinedAttr, combinedStrSizes);
				boolean smallFlag = true;
				for(int i=0;i<numTables;i++){
					if(tempTuple.getIntFld(getTupleOffset(i+1))!=kTuple.getIntFld(getTupleOffset(i+1))){
						smallFlag = false;
					}
				}
				if(!smallFlag){
					count++;
				}
				tempTuple = scan.getNext(rid);
			}
			if(count==kResultsFile.getRecCnt() && fullTuple(kTuple, combinedAttr, joinColumns)){
				//System.out.println("inserting record : ");
				kTuple.print(combinedAttr);
				kResultsFile.insertRecord(kTuple.getTupleByteArray());
			}
		}
		catch(Exception e){
			System.out.println("Exception in checkAndInsert");
			e.printStackTrace();
		}
	}
	private void deleteFromInterFile(RID delRID, int relation){
		try{

			FileScan fileScan = null;
			try {
				fileScan = new FileScan("TempResults.in", combinedAttr,
						combinedStrSizes, (short) combinedAttrCount,
						combinedAttrCount, combinedProjection, null);
				
			Tuple delTuple = fileScan.get_next();
			while(delTuple!=null){
				RID tempRID = ConstantVars.getGlobalRID();
				int intKey=0;
				int fieldIndex =getTupleOffset(relation)+inputRelations[relation].length-1;
				float delScore = delTuple.getFloFld(fieldIndex);
				for(int r=getTupleOffset(relation);r<fieldIndex;r++){
					switch(inputRelations[relation][r-getTupleOffset(relation)].attrType){
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
				}
				delTuple.setFloFld(superAttrTypes.le, delTuple.getFloFld(superAttrTypes.length)*numberOfTables-delScore);
				if(emptyTuple(delTuple,combinedAttr,joinColumns)){
					interTAtuples.deleteRecord(tempRID);
					interBTF[relation].Delete(new IntegerKey(intKey), tempRID);
				}
				else{
					interTAtuples.updateRecord(tempRID, delTuple);
				}
				delTuple = fileScan.get_next();
			}
			//System.out.println("After delete " + interTAtuples.getRecCnt());
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
					if(tuple.getIntFld(getTupleOffset[i]+joiningOn[i]+1)!=0)
						returnVal=false;
					break;
				case AttrType.attrString:
					if(!tuple.getStrFld(tupleOffsets[i]+joiningOn[i]+1).equals(""))
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
*/	private boolean isTopKCandidate(Tuple topKTuple,int relNum)
	{
		//System.out.println("In TopK candidate");
		try {
			//topKTuple.print(combinedAttr);
		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		try {
			float minscore = topKTuple.getFloFld(getTupleOffset(relNum)+inputRelations[relNum].length-1);
			if(kMinimums[relNum]>minscore)
				kMinimums[relNum] =minscore;
		} catch (FieldNumberOutOfBoundException | IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		try {
			float score = topKTuple.getFloFld(combinedAttrCount-1);
			FileScan fileScan = null;
			try {
				fileScan = new FileScan("TempResults.in", combinedAttr,
						combinedStrSizes, (short) combinedAttrCount,
						combinedAttrCount, combinedProjection, null);
			TupleOrder order = new TupleOrder(TupleOrder.Descending);
			Iterator topIterator = null;
			try {
				topIterator = new AdvancedSort(combinedAttr,
						(short) (combinedAttrCount), combinedStrSizes, fileScan,
						combinedAttrCount-1, order, 4, 30);
			} catch (SortException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
				Tuple newTuple = null;
				int count = kCounter;
				while((newTuple = topIterator.get_next())!=null)
				{	
					count--;
					float TupleScore = newTuple.getFloFld(combinedAttrCount-1);
					int noOfRelationsChecked = newTuple.getIntFld(combinedAttrCount-2);
					if(score<=TupleScore && noOfRelationsChecked==numTables)
					{
						RID rid = ConstantVars.getGlobalRID();
						int RIDVal = rid.pageNo.pid*1000 + rid.slotNo;
						kCounter=kCounter-1;
						AttrType[] newAttrType = new AttrType[combinedAttrCount+1];
						for(int i=0;i<newAttrType.length-1;i++){
							newAttrType[i] = combinedAttr[i];
						}
						newAttrType[combinedAttrCount] = new AttrType(AttrType.attrInteger);
						//System.out.println("Printing Top K candidates");
						updateResultsFile(newTuple,rid);
						return true;
					}
					if(count <=0)
						break;
				}
				fileScan.close();
				topIterator.close();
			} catch (Exception ex) {
				ex.printStackTrace();
			}
		} catch (FieldNumberOutOfBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return false;
	}

	private void createHeapFiles() {
		try {
			kResultsFile = new Heapfile("topKResults.in");
		} catch (HFException e1) {
			e1.printStackTrace();
		} catch (HFBufMgrException e1) {
			e1.printStackTrace();
		} catch (HFDiskMgrException e1) {
			e1.printStackTrace();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}

	public void printResults() {
		FileScan fileScan = null;
		try {
			fileScan = new FileScan("topKResults.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
			Tuple newTuple = null;
		} catch (Exception ex) {
			ex.printStackTrace();
		}
		System.out.println("Printing Results in PrintResults");
		System.out.println("----------------------------------");
		TupleOrder order = new TupleOrder(TupleOrder.Descending);
		Iterator topIterator = null;
		try {
			topIterator = new Sort(combinedAttr,
					(short) combinedAttrCount, combinedStrSizes, fileScan,
					combinedAttrCount, order, 4, 20);
			
		} catch (SortException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
			try {
				Tuple tup = null;
				while((tup = topIterator.get_next())!=null)
				{	
					tup.print(combinedTuple.attr_Types);
				}
			}
			catch (Exception ex) {
				ex.printStackTrace();
			}
			System.out.println("-------------------------------------------");
		try {
			topIterator.close();
		} catch (JoinsException | SortException | IndexException | IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		fileScan.close();
		System.out.println("Completed Printing");
	}
	private int checkIndicator()
	{
		boolean temp = false;
		float maxIndicator=-1;
		float indicator =-1;
		int tableIndex =-1;
		for(int i=0;i<numTables;i++)
		{
			indicator = indicators[i];
			if(indicator>maxIndicator)
			{
				maxIndicator = indicator;
				tableIndex =i;
			}
		}
		arr[tableIndex]++;
		for(int i=0;i<numTables;i++)
		{
			if(arr[i]>numTables)
			{
				if(i==numTables-1)
					tableIndex =0;
				else
					tableIndex =i+1;
				temp =true;
				break;
			}
			
		}
		if(temp)
		{
			for(int i=0;i<numTables;i++)
			{
				arr[i]=0;
			}
			temp =false;
		}
		return tableIndex;
	}
	private int callIndicatorFunction()
	{
		if(!flag)
		{
			calculateIndicator();
		}
		flag = false;
		int tableIndex = checkIndicator();
		/*System.out.println("Max Indicator is"+maxIndicator);
		System.out.println("Table Index is"+tableIndex);*/		
		Tuple fileTuple = new Tuple();
		Tuple scanTuple = new Tuple();
		try {
			fileTuple = iterators[tableIndex].get_next();
		} catch (JoinsException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IndexException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (InvalidTupleSizeException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (InvalidTypeException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (PageNotReadException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (TupleUtilsException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (PredEvalException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (SortException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (LowMemException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (UnknowAttrType e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (UnknownKeyTypeException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (Exception e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		AttrType keyAttrType = new AttrType(
				inputRelations[0][joinColumns[0]].attrType);
		String strKey = "";
		try {
			scanTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
		} catch (InvalidTypeException | InvalidTupleSizeException | IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		int keySize = 4;
		BTreeFile callBtf1 = null;
		try {
			switch (inputRelations[0][joinColumns[0]].attrType) {
			case AttrType.attrInteger:
				strKey = String.valueOf(fileTuple
						.getIntFld(joinColumns[tableIndex] + 1));
				keySize = 4;
				break;
			case AttrType.attrString:
				strKey = fileTuple
				.getStrFld(joinColumns[tableIndex] + 1);
				keySize = 20;
				break;
			}
			callBtf1 = new BTreeFile(
					"BTreeIndex",
					inputRelations[0][joinColumns[0]].attrType,
					keySize, 1);

		} catch (Exception e) {
			e.printStackTrace();
			Runtime.getRuntime().exit(1);
		}
		Scan scan = null;
		RID sScanRid = new RID();
		String sTupleKey = "";
		int tupleKey = 0;
		Tuple temp1 = null;
		try {
			scan = new Scan(tempFile);
			temp1 = scan.getNext(sScanRid);
		} catch (Exception e) {
			e.printStackTrace();
		} 
		while (temp1 != null) {
			scanTuple.tupleCopy(temp1);
			try {
				switch (inputRelations[0][joinColumns[0]].attrType) {
				case AttrType.attrInteger:
					tupleKey = scanTuple
					.getIntFld(combinedAttrCount);
					callBtf1.insert(new IntegerKey(tupleKey), sScanRid);
					break;
				case AttrType.attrString:
					sTupleKey = scanTuple
					.getStrFld(combinedAttrCount);
					callBtf1.insert(new StringKey(sTupleKey), sScanRid);
					break;
				}
				temp1 = scan.getNext(sScanRid);

			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		int count =0;
		count += sequentialAccess(fileTuple, keyAttrType,
				strKey, tableIndex);
		scan.closescan();
		
		try {
			callBtf1.close();
		} catch (PageUnpinnedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvalidFrameNumberException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (HashEntryNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ReplacerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return count;
	}

	public void topKResults() {
		int count = 0;
		int k = 2*numTables;
		counter = knumTuples;
		Tuple fileTuple = new Tuple();
		Tuple scanTuple = new Tuple();
		AttrType keyAttrType = new AttrType(
				inputRelations[0][joinColumns[0]].attrType);
		while (count < knumTuples) {
			if(k<=0)
			{
				count+=callIndicatorFunction();
				counter = knumTuples-count;
			}
			else
			{
				for (int relNum = 0; relNum < numTables; relNum++) {

					try {
						fileTuple = iterators[relNum].get_next();
						System.out.println("File Tuple in Print Relations is"+relNum);
						fileTuple.print(inputRelations[relNum]);
						if (fileTuple == null)
							continue;
						String strKey = "";
						scanTuple.setHdr((short) combinedAttrCount, combinedAttr,
								combinedStrSizes);
						int keySize = 4;
						try {
							switch (inputRelations[relNum][joinColumns[relNum]].attrType) {
							case AttrType.attrInteger:
								strKey = String.valueOf(fileTuple
										.getIntFld(joinColumns[relNum] + 1));
								keySize = 4;
								break;
							case AttrType.attrString:
								strKey = fileTuple
								.getStrFld(joinColumns[relNum] + 1);
								keySize = 20;
								break;
							}
							btf1 = new BTreeFile(
									"BTreeIndex",
									inputRelations[relNum][joinColumns[relNum]].attrType,
									keySize, 1);
							
						} catch (Exception e) {
							e.printStackTrace();
							Runtime.getRuntime().exit(1);
						}
						Scan scan = null;
						RID sScanRid = new RID();
						String sTupleKey = "";
						int tupleKey = 0;
						Tuple temp1 = null;
						try {
							scan = new Scan(tempFile);
							temp1 = scan.getNext(sScanRid);
						} catch (Exception e) {
							e.printStackTrace();
						} 
						while (temp1 != null) {
							scanTuple.tupleCopy(temp1);
							//System.out.println("In While Loop");
							try {
								switch (inputRelations[relNum][joinColumns[relNum]].attrType) {
								case AttrType.attrInteger:
									tupleKey = scanTuple
									.getIntFld(combinedAttrCount);
									btf1.insert(new IntegerKey(tupleKey), sScanRid);
									break;
								case AttrType.attrString:
									sTupleKey = scanTuple
									.getStrFld(combinedAttrCount);
									//System.out.println("BTF Keys");
									btf1.insert(new StringKey(sTupleKey), sScanRid);
									
									break;
								}
								temp1 = scan.getNext(sScanRid);
								
							} catch (Exception e) {
								e.printStackTrace();
							}
						}	
						scan.closescan();
						if(roundRobin ==1)
						{
							if(k>0)
							{
								count +=sequentialAccess(fileTuple,keyAttrType,strKey,relNum);
								k--;
							}
						}
						else
						{
							count += sequentialAccess(fileTuple, keyAttrType,
									strKey, relNum);
						}
						btf1.close();
					} catch (Exception e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				
				}
			}
		}
		printResults();
	}
	
	public void printTempFile()
	{
		FileScan fileScan = null;
		try {
			fileScan = new FileScan("TempResults.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
		} catch (Exception ex) {
			ex.printStackTrace();
		}
		try {
			Tuple tup = null;
			while((tup = fileScan.get_next())!=null)
				{	
					tup.print(combinedTuple.attr_Types);
				}
			}
			catch (Exception ex) {
				ex.printStackTrace();
			}
		fileScan.close();
		System.out.println("Completed Printing");

	}
	private void updateResultsFile(Tuple fileTuple,RID rid)
	{
		calculateIndicator();
		flag = true;
		try {
			Tuple tup = new Tuple();
			try {
				tup.setHdr((short)combinedAttrCount, combinedAttr,(short[])combinedStrSizes);
			} catch (InvalidTypeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			int attrLength = fileTuple.attr_Types.length;
			attrLength =attrLength -1;
			for (int tField = 1; tField <= attrLength; tField++) {
				switch (combinedAttr[tField - 1].attrType) {
				case AttrType.attrInteger:
					try {
						tup.setIntFld(tField, fileTuple.getIntFld(tField));

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
						
						tup.setFloFld(tField, fileTuple.getFloFld(tField));
						
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
						tup.setStrFld(tField, fileTuple.getStrFld(tField));
						
					} catch (FieldNumberOutOfBoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					} catch (IOException e) {
						e.printStackTrace();
					}
					break;
				}
			}
			kResultsFile.insertRecord(tup.getTupleByteArray());
		} catch (InvalidSlotNumberException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvalidTupleSizeException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SpaceNotAvailableException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (HFException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (HFBufMgrException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (HFDiskMgrException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		try {
			int RidVal = fileTuple.getIntFld(combinedAttrCount+1);
			int slotNo = RidVal%1000;
			int pageNo =(RidVal-slotNo)/1000;
			RID ridnew = new RID();
			ridnew.pageNo = new PageId(pageNo);
			ridnew.slotNo = slotNo;
			tempFile.deleteRecord(ridnew);
			/*
			AttrType keyAttrType = new AttrType(
					inputRelations[0][joinColumns[0]].attrType);
			switch(keyAttrType.attrType)
			{
				case AttrType.attrInteger:
					int key = fileTuple.getIntFld(combinedAttrCount);
					btf1.Delete(new IntegerKey(key), ridnew);
					break;
				case AttrType.attrString:
					String strkey = fileTuple.getStrFld(combinedAttrCount);
					btf1.Delete(new StringKey(strkey), ridnew);
			}
			*/
			
		} catch (InvalidSlotNumberException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvalidTupleSizeException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (HFException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (HFBufMgrException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (HFDiskMgrException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private boolean isRelationExist(AttrType keyAttrType,int relNum,String strKey,Tuple fileTuple)
	{
		int keySize = 4;
		String str ="";
		Tuple scanTuple = new Tuple();
		try {
			scanTuple.setHdr((short) combinedAttrCount, combinedAttr,
					combinedStrSizes);
			try {
				switch (inputRelations[relNum][joinColumns[relNum]].attrType) {
				case AttrType.attrInteger:
					str = String.valueOf(fileTuple
							.getIntFld(joinColumns[relNum] + 1));
					keySize = 4;
					break;
				case AttrType.attrString:
					str = fileTuple
					.getStrFld(joinColumns[relNum] + 1);
					keySize = 20;
					break;
				}
			}
			catch(Exception ex)
			{
				ex.printStackTrace();
			}

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
		BTreeFile sortBtf = null;

		try {
			sortBtf = new BTreeFile(
					"KTreeIndex",
					inputRelations[0][joinColumns[0]].attrType,
					keySize, 1);
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
		Scan scan = null;
		RID sScanRid = new RID();
		String sTupleKey = "";
		int tupleKey = 0;
		Tuple temp1 = null;
		try {
			scan = new Scan(kResultsFile);
			temp1 = scan.getNext(sScanRid);
		} catch (Exception e) {
			e.printStackTrace();
		} 
		while (temp1 != null) {
			scanTuple.tupleCopy(temp1);
			try {
				switch (inputRelations[0][joinColumns[0]].attrType) {
				case AttrType.attrInteger:
					tupleKey = scanTuple
					.getIntFld(combinedAttrCount);
					sortBtf.insert(new IntegerKey(tupleKey), sScanRid);
					break;
				case AttrType.attrString:
					sTupleKey = scanTuple
					.getStrFld(combinedAttrCount);
					sortBtf.insert(new StringKey(sTupleKey), sScanRid);
					break;
				}
				temp1 = scan.getNext(sScanRid);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}	
		scan.closescan();
		IndexScan tempScan = null;
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
		/*
		AttrType[] newAttrType = new AttrType[combinedAttrCount+1];
		for(int i=0;i<newAttrType.length-1;i++){
			newAttrType[i] = combinedAttr[i];
		}
		newAttrType[combinedAttrCount] = new AttrType(AttrType.attrInteger);
		*/
		try {
			tempScan = new IndexScan(new IndexType(IndexType.B_Index),
					"topKResults.in", "KTreeIndex", combinedAttr,
					combinedStrSizes, combinedAttrCount, combinedAttrCount,
					combinedProjection, randomExpr, combinedAttrCount-1, false);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Tuple temp = null;
		RID prevRID = new RID();
		boolean keyExists= false;
		
		
		
		try {
			HashMap<String, Boolean> randomMap = new HashMap<String, Boolean>();
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
				updateTuple(fileTuple, combinedTuple, relNum,
							getTupleOffset(relNum));
				try {
						tempFile.insertRecord(combinedTuple.getTupleByteArray());
					} catch (InvalidSlotNumberException
							| InvalidTupleSizeException
							| SpaceNotAvailableException | HFException
							| HFBufMgrException | HFDiskMgrException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					
					/*System.out.println("Printing Results");
					System.out.println("-----------------------------------------------");
					printResults();
					System.out.println("-----------------------------------------------");*/
			}
			tempScan.close();
			if(keyExists)
			{
				updateRemainingRelations(fileTuple, relNum);
				return true;
			}
			try {
				sortBtf.close();
			} catch (PageUnpinnedException | InvalidFrameNumberException
					| HashEntryNotFoundException | ReplacerException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} catch (IndexException | UnknownKeyTypeException | IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return false;
	}
	private int sequentialAccess(Tuple fileTuple, AttrType keyAttrType,
			String strKey, int relNum) {
		combinedTuple = new Tuple();
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
					updateTuple(fileTuple, combinedTuple, relNum,
							getTupleOffset(relNum));
					//combinedTuple.print(combinedAttr);
					tempFile.insertRecord(combinedTuple.getTupleByteArray());
					updateRemainingRelations(fileTuple, relNum);
					/*System.out.println("Printing Results");
					System.out.println("-----------------------------------------------");
					printTempFile();
					System.out.println("-----------------------------------------------");*/
				} else {
					RID updateRid = ConstantVars.getGlobalRID();
					updateTuple(fileTuple, combinedTuple, relNum,
							getTupleOffset(relNum));
					int fieldValue = combinedTuple.getIntFld(combinedAttrCount-2);
					combinedTuple.setIntFld(combinedAttrCount - 2,fieldValue+1);
					//combinedTuple.print(combinedAttr);
					tempFile.updateRecord(updateRid, combinedTuple);
					updateRemainingRelations(fileTuple,relNum);
					/*System.out.println("Printing Results");
					System.out.println("-----------------------------------------------");
					printTempFile();
					System.out.println("-----------------------------------------------");*/
				}
				if (combinedTuple.getIntFld(combinedAttrCount - 2) == numTables &&isTopKCandidate(combinedTuple,relNum)) {
					count++;
					//printResults();
					break;
				}
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		if (!keyExists) {
			if(!isRelationExist(keyAttrType,relNum,strKey,fileTuple))
			{
				updateTuple(fileTuple, combinedTuple, relNum,
					getTupleOffset(relNum));
				try {
					combinedTuple.setIntFld(combinedAttrCount - 2,
						combinedTuple.getIntFld(combinedAttrCount - 2) + 1);
					if (keyAttrType.attrType == AttrType.attrInteger) {
						combinedTuple.setIntFld(combinedAttrCount,
							Integer.parseInt(strKey));
					} else if (keyAttrType.attrType == AttrType.attrString) {
					combinedTuple.setStrFld(combinedAttrCount, strKey);
					}
				//combinedTuple.print(combinedAttr);
				tempFile.insertRecord(combinedTuple.getTupleByteArray());
				updateRemainingRelations(fileTuple, relNum);
				/*System.out.println("Printing Results");
				System.out.println("-----------------------------------------------");
				printTempFile();
				System.out.println("-----------------------------------------------");*/
			} catch (Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			}
		}
		try {
			tempScan.close();
		} catch (IndexException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		// TODO Auto-generated method stub
		return count;
	}
	private void updateRemainingRelations(Tuple fileTuple, int relNum) {
		Tuple tuple = new Tuple(combinedTuple);
		AttrType type = inputRelations[0][joinColumns[0]];
		Tuple temp = null;
		FileScan scan = null;
		try {
			scan = new FileScan("TempResults.in", combinedAttr,
					combinedStrSizes, (short) combinedAttrCount,
					combinedAttrCount, combinedProjection, null);
		} catch (Exception ex) {
			ex.printStackTrace();
		} 
		try {
			RID rid = new RID();
			while ((temp = scan.get_next()) != null) {
				tuple.tupleCopy(temp);
				//tuple.print(combinedAttr);
				for(int rel=0;rel<numTables;rel++)
				{
					int fieldIndex = getTupleOffset(rel) + joinColumns[rel];
					int attrLength = inputRelations[rel].length
							+ getTupleOffset(rel)-1;

					
					rid = ConstantVars.getGlobalRID();
					switch (type.attrType) {
					case AttrType.attrInteger:
						try {
							float score = minScores[rel];
							if (tuple.getIntFld(fieldIndex) == 0) {
								tuple.setFloFld(attrLength, score);
							}
						} catch (Exception ex) {
							ex.printStackTrace();
						}
						break;
					case AttrType.attrString:
						if (tuple.getStrFld(fieldIndex).equals("")) {
							tuple.setFloFld(attrLength, minScores[rel]);
						}
						break;
					}
				}
				float tempScore = 0;
				int fieldLength = 0;
				for (int i = 0; i < numTables; i++) {
					fieldLength += inputRelations[i].length;
					try {
						tempScore += tuple.getFloFld(fieldLength);
					} catch (FieldNumberOutOfBoundException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
				tempScore = tempScore / numTables;
				try {
					tuple.setFloFld(combinedAttrCount - 1,
							tempScore);
				} catch (Exception ex) {
					System.out.println("Exception Caught");
				}
				//tuple.print(combinedAttr);
				tempFile.updateRecord(rid, tuple);
			}
		} catch (Exception ex) {
			ex.printStackTrace();
		}
		scan.close();
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
			switch (inputRelations[tableIndex][tField - 1].attrType) {
			case AttrType.attrInteger:
				try {
					outTuple.setIntFld(offset, inTuple.getIntFld(fieldCount));
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
					float score = inTuple.getFloFld(attrLength);
					outTuple.setFloFld(offset, inTuple.getFloFld(fieldCount));
					if(tField == attrLength)
					{
						if(minScores[tableIndex]>score)
							minScores[tableIndex] = score;
					}
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
		float tempScore = 0;
		int fieldLength = 0;
		for (int i = 0; i < numTables; i++) {
			fieldLength += inputRelations[i].length;
			try {
				tempScore += outTuple.getFloFld(fieldLength);
			} catch (FieldNumberOutOfBoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		tempScore = tempScore / numTables;
		try {
			outTuple.setFloFld(combinedAttrCount - 1, tempScore);
		} catch (Exception ex) {
			System.out.println("Exception Caught");
		}
	}
	public boolean relationExists(int relNum, String strKey, Tuple jTuple) {
		int keyOffset = getTupleOffset(relNum)+joinColumns[relNum];
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
	public void calculateIndicator()
	{
		FldSpec[] fldProjectionList = new FldSpec[combinedAttrCount];
		for (int j = 0; j < fldProjectionList.length; j++) {
			fldProjectionList[j] = new FldSpec(new RelSpec(RelSpec.outer), j + 1);
		}
		try {
			float[] prevScore = new float[this.numTables];
			float[] currScore = new float[this.numTables];
			/*System.out.println("In Indicator Function");
			System.out.println("--------------------------------");
			printTempFile();
			System.out.println("--------------------------------");*/
			Tuple tempTuple;
			// Reset M.
			for (int j = 0; j < numTables; j++) {
				this.M[j] = 0;
			}
			FileScan fScan = null;
			try {
				fScan = new FileScan("TempResults.in", combinedAttr,
						combinedStrSizes, (short) combinedAttrCount,
						combinedAttrCount, combinedProjection, null);
			} catch (Exception ex) {
				ex.printStackTrace();
			}
			TupleOrder order = new TupleOrder(TupleOrder.Descending);
			Iterator topIterator = null;
			try {
				topIterator = new Sort(combinedAttr,
						(short) combinedAttrCount, combinedStrSizes, fScan,
						combinedAttrCount-1, order, 4, 20);
			} catch (SortException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			int count = counter;
			while ((tempTuple = topIterator.get_next()) != null) {
				if(count <= 1)
					break;
				int fieldLength = tempTuple.getIntFld(combinedAttrCount-1);
				if(fieldLength == numTables)
					continue;
				count--;
				Tuple tempStreamTuple = new Tuple(combinedTuple);
				tempStreamTuple.tupleCopy(tempTuple);
				int sum = 0;
				for (int j = 0; j < numTables; j++) {
					AttrType type = inputRelations[j][joinColumns[j]];
					int fieldIndex = getTupleOffset(j);
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
						this.M[j]++;
					} 
					else {
						sum++;
					}
				}
			}
			topIterator.close();
			fScan.close();
			FileScan fileScan =
					new FileScan("TempResults.in",combinedAttr, combinedStrSizes, (short) combinedAttrCount,
							combinedAttrCount, fldProjectionList, null);
			
			while ((tempTuple = fileScan.get_next()) != null) {
				Tuple tempStreamTuple = new Tuple(combinedTuple);
				tempStreamTuple.tupleCopy(tempTuple);
				//tempStreamTuple.print(combinedAttr);
				for (int j = 0; j < numTables; j++) {
					int flag = -1;
					AttrType type = inputRelations[j][joinColumns[j]];
					int fieldIndex = getTupleOffset(j);
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
			float dervOfAvgFunc = (float) (1.0f / numTables);
			// Calculate the indicators for each stream.
			for (int i = 0; i < numTables; i++) {
				double diff = (double) prevScore[i] - currScore[i];	
				this.indicators[i] = (float) (M[i] * dervOfAvgFunc * diff);
			}
		} 
		catch (Exception e) {

			e.printStackTrace();
		}
	}
}
