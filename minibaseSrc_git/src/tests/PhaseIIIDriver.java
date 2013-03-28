package tests;

import global.AttrOperator;
import global.AttrType;
import global.ExcelParser;
import global.GlobalConst;
import global.IndexType;
import global.RID;
import global.SystemDefs;
import global.TupleOrder;
import heap.Heapfile;
import heap.Scan;
import heap.Tuple;
import index.IndexScan;
import iterator.CondExpr;
import iterator.DuplElim;
import iterator.FileScan;
import iterator.FldSpec;
import iterator.Iterator;
import iterator.RelSpec;
import iterator.Sort;
import iterator.TopNestedLoopsJoins;
import iterator.TopRankJoin;
import iterator.TopSortMerge;
import iterator.TopTAJoin;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.Vector;

import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.poifs.filesystem.POIFSFileSystem;

import btree.BTreeFile;
import btree.IntegerKey;
import btree.RealKey;
import btree.StringKey;

public class PhaseIIIDriver implements GlobalConst{

	private static boolean OK = true;
	private static boolean FAIL = false;
	SystemDefs sysdef;
	public PhaseIIIDriver() {
	    
	    //build Sailor, Boats, Reserves table
	    	    
	    String dbpath = System.getProperty("user.name")+".minibase.jointestdb"; 
	    String logpath = System.getProperty("user.name")+".joinlog";

	    String remove_cmd = "/bin/rm -rf ";
	    String remove_logcmd = remove_cmd + logpath;
	    String remove_dbcmd = remove_cmd + dbpath;
	    String remove_joincmd = remove_cmd + dbpath;

	    try {
	      Runtime.getRuntime().exec(remove_logcmd);
	      Runtime.getRuntime().exec(remove_dbcmd);
	      Runtime.getRuntime().exec(remove_joincmd);
	    }
	    catch (IOException e) {
	      System.err.println (""+e);
	    }

	   
	    /*
	    ExtendedSystemDefs extSysDef = 
	      new ExtendedSystemDefs( "/tmp/minibase.jointestdb", "/tmp/joinlog",
				      1000,500,200,"Clock");
	    */

	    sysdef = new SystemDefs( dbpath, 1000, NUMBUF, "Clock" );
	    
	}

	
	
	/**
	 * TopSortMerge
	 */
	
	
	/**
	 * TopRankJoin
	 */
	public static void processTopTAJoin(){
		
		Scanner scanner = new Scanner(System.in);
		boolean status = true;
		try{
			System.out.println("Enter number of tables to be joined");
			int numOfTables = scanner.nextInt();
			AttrType [][] attrTypeList = new AttrType[numOfTables][];
			int [] numOfColsList = new int[numOfTables];
			short [][] stringSizesList = new short[numOfTables][];
			int [] joinedColList = new int[numOfTables]; 
			Iterator [] iteratorList = new Iterator[numOfTables];
			AttrType [] indexAttrType = new AttrType[numOfTables];
			String [] indexNameList = new String[numOfTables];
			IndexType[] b_index = new IndexType[numOfTables];
		    String[] fileNames = new String[numOfTables];
			String [] tableNameList = new String[numOfTables];
			ArrayList<FldSpec> list = new ArrayList<FldSpec>();
			FldSpec[] newProjList = null;
			//ArrayList colNameList = new ArrayList();
			scanner.nextLine();
			
			FldSpec[] projList = new FldSpec[20];
			FldSpec[][] projTableSpecificList = new FldSpec[numOfTables][20];
		    RelSpec rel = null;
		    //projlist[1] = new FldSpec(rel, 2);
			
			int projlistIndex = 0;	//Gives number of output attribute columns in the projection
			for(int k=0;k<numOfTables;k++)
			{
				boolean flag = true;
				System.out.println("Enter name for Table"+(k+1));
				String tableName = scanner.nextLine();
				tableNameList[k] = tableName;
				System.out.println("Enter file location");
				String fileLoc1 = scanner.nextLine();
			
				System.out.println("Enter the column number in the table to be joined");
				int joinColNumber = scanner.nextInt();
				
				joinedColList[k] = joinColNumber-1; 
				//SOC
				HSSFWorkbook workBook = null; 
				File file  = new File(fileLoc1);
				InputStream excelDocumentStream = null;
				try 
				{
					excelDocumentStream = new FileInputStream(file);
					POIFSFileSystem fsPOI = new POIFSFileSystem(new BufferedInputStream(excelDocumentStream));
					workBook = new HSSFWorkbook(fsPOI);         
					ExcelParser parser = new ExcelParser(workBook.getSheetAt(0));
					String [] res;
		       		       
					Heapfile topFile = new Heapfile(tableName+".in");
						       
					Tuple t = new Tuple();
					
					System.out.println("Enter the number of Columns in the table");
					int numOfColms = scanner.nextInt();/*parser.getNumberOfColms()*/;
					
					//System.out.println("noOfColms ="+numOfColms);
					numOfColsList[k] = numOfColms;
					
					AttrType [] Stypes = new AttrType[numOfColms];
					int col=0;
					int numOfStringCol =0;
					while(col<numOfColms){
						System.out.println("Enter the datatype of column["+(col+1)+"]\n 0-> String\n 1-> Integer\n 2->Real");
						int attrType = scanner.nextInt();
						switch(attrType){
							case 0: Stypes[col] = new AttrType(AttrType.attrString);
						        numOfStringCol++;
						        break;
						
							case 1: Stypes[col] = new AttrType(AttrType.attrInteger);
								break;
							
							case 2: Stypes[col] = new AttrType(AttrType.attrReal);
								break;
							
							default: System.out.println("Invalid option");
								 System.exit(0);
						}
						
					//Saves the attribute type of the column to be joined which indicates the index type
					if(col==joinColNumber-1)
						indexAttrType[k] = Stypes[col];
					
					col++;
					}
					
					attrTypeList[k] = Stypes;
					
					short [] Ssizes = new short [numOfStringCol];
					for(int e=0;e<numOfStringCol;e++)
						Ssizes[e] = 20;  					
					stringSizesList[k] = Ssizes;
					
					try {
						t.setHdr((short) numOfColms,Stypes, Ssizes);
					}
					catch (Exception e) {
						System.err.println("*** error in Tuple.setHdr() ***");
						status = false;
						e.printStackTrace();
					}
		       		       
					RID rid = null;
					res = parser.splitLine();
					while (res !=null && res.length!=0)
					{
						int i;
						for (i = 0; i < Stypes.length-1; i++)
						{
							//System.out.println("Token Found [new folder" + res[i] + "]");
							AttrType attr= Stypes[i];
							int type = attr.attrType;
							//System.out.println("type = "+type);
							switch(type){
					   			case AttrType.attrString: t.setStrFld(i+1, res[i]);
					   				break;
					   			case AttrType.attrInteger: t.setIntFld(i+1, Integer.parseInt(res[i]));
					   				break;
					   			case AttrType.attrReal: t.setFloFld(i+1, Float.parseFloat(res[i]));
					   				break;
							}
						
					   
							
						}
						
						if(i==Stypes.length-1){
							//System.out.println("Score =" + res[i]);
							t.setScore(Float.parseFloat(res[i]));
							t.setFloFld(i+1, Float.parseFloat(res[i]));
						}
						//t.print(Stypes);
						rid = topFile.insertRecord(t.getTupleByteArray());
						res = parser.splitLine();
					}
					excelDocumentStream.close();
		       
		       
					// create an scan on the heapfile
				    Scan scan = null;
				    
				    try {
				      scan = new Scan(topFile);
				    }
				    catch (Exception e) {
				      status = false;
				      e.printStackTrace();
				      Runtime.getRuntime().exit(1);
				    }

				    // create the index file
				    BTreeFile btf = null;
				    try {
				      btf = new BTreeFile(tableName+"_BTreeIndex", indexAttrType[k].attrType, GlobalConst.INDEX_REC_LEN, 1/*delete*/); 
				      indexNameList[k] = tableName+"_BTreeIndex";
				      b_index[k] = new IndexType(IndexType.B_Index);
				      fileNames[k] = tableNameList[k]+".in";
				    }
				    catch (Exception e) {
				      status = false;
				      e.printStackTrace();
				      Runtime.getRuntime().exit(1);
				    }

				    System.out.println("BTreeIndex created successfully.\n"); 
				    
				    RID rid1 = new RID();
				    //String key = null;
				    Tuple temp = null;
				    
				    try {
				      temp = scan.getNext(rid1);
				    }
				    catch (Exception e) {
				      status = false;
				      e.printStackTrace();
				    }
				    while ( temp != null) {
				      t.tupleCopy(temp);
				      
				      try {
				    	  //System.out.println("indexAttrType[k].attrType ="+indexAttrType[k].attrType);
				    	  //System.out.println("t.getIntFld ="+t.getIntFld(joinColNumber));
				    	  switch(indexAttrType[k].attrType){
				   			case AttrType.attrString: String keyString = t.getStrFld(joinColNumber);
				   									  btf.insert(new StringKey(keyString), rid1); 
				   										break;
				   			case AttrType.attrInteger: int keyInt = t.getIntFld(joinColNumber);
				   										btf.insert(new IntegerKey(keyInt), rid1); 
				   										break;
				   			case AttrType.attrReal: float keyFloat = t.getFloFld(joinColNumber);
				   									btf.insert(new RealKey(keyFloat), rid1); 
				   										break;
						}
				   		  				    	  					
				      }
				      catch (Exception e) {
				    	  status = false;
				    	  e.printStackTrace();
				      }
				     try {
				    	 temp = scan.getNext(rid1);
				      }
				      catch (Exception e) {
				    	  status = false;
				    	  e.printStackTrace();
				      }
				    }
				    
				    // close the file scan
				    scan.closescan();
				    
				    System.out.println("BTreeIndex file created successfully.\n"); 
				    
				    rel = new RelSpec(k);
				    int projColTableSpecificOffset= 0;
				    String moreColFlag;
				    int [] colNumList = new int[20];
				    //int count=1;
				    while(flag){
				    	
				    	System.out.println("Enter the column number to be projected from this table");
						int colNum = scanner.nextInt();
						scanner.nextLine();
//						/System.out.println("projlistIndex="+projlistIndex); 
						FldSpec fld = new FldSpec(rel, colNum);
						list.add(fld);
						projList[projlistIndex] = new FldSpec(rel, colNum);
						colNumList[projColTableSpecificOffset]=colNum;
						projColTableSpecificOffset++;
						
						System.out.println("Are there more columns to be projected from this table (Y/N)?");
						moreColFlag = scanner.nextLine();
						
						if(moreColFlag.equalsIgnoreCase("Y"))
							flag=true;
						
						else if(moreColFlag.equalsIgnoreCase("N"))
							flag=false;
						projlistIndex++;
						
						
				    }
				    newProjList = new FldSpec[list.size()];
				    for(int i = 0;i<list.size();i++){
				    	newProjList[i] = list.get(i);
				    }
				    projlistIndex = newProjList.length;
				    FldSpec[] pList = new FldSpec[projColTableSpecificOffset];
				    for(int l=0;l<projColTableSpecificOffset;l++){
				    	pList[l] = new FldSpec(rel, colNumList[l]);
				    	 
				    }
				    projTableSpecificList[k] = pList;
				    
			  }
		      catch(Exception e)
		      {
		        e.printStackTrace();
		      }
		 
			  	
			  	
			//EOC
		    //scanner.nextLine();
		    
		}
		//System.out.println("projlistIndex ="+projlistIndex);
		System.out.println("Enter the number of conditions in the where clause ");
				
		int numCondExpr = scanner.nextInt();
		scanner.nextLine();
		String [] conditionString = new String[numCondExpr];
		for(int a=0; a<numCondExpr ; a++)
		{
			System.out.println("Enter the "+(a+1)+" condition in the following format\n" + 
					"<**TableNumber**>.<**ColumnNumber**> <**operator**> <**TableNumber**>.<**ColumnNumber/Constant**> ");
			conditionString[a] = scanner.nextLine();
				
		}
		for(int a=0; a<numCondExpr ; a++){
				
			System.out.println(conditionString[a]);
			if(a!=numCondExpr-1){
				System.out.println("AND");
			}
		}
		
		/*for(int i=0;i<attrTypeList.length;i++){
			AttrType[] attr = attrTypeList[i];
			System.out.println("i ="+i);
			for(int j=0;j<attr.length;j++){
				System.out.println("attr type ="+attr[j].attrType);
			}
		}*/
		
		CondExpr [] condExprList = new CondExpr[numCondExpr+1];
		
		for(int a=0;a<condExprList.length-1;a++){
				condExprList[a] = new CondExpr();
				String condString = conditionString[a];
				condExprList[a].next  = null;
				int beginIndex = 0;
				int endIndex = condString.indexOf(".", 0);
				String tableNumString = condString.substring(beginIndex, endIndex);
				int tableNum = Integer.parseInt(tableNumString);
				int endIndex1 = condString.indexOf(" ",endIndex);
				String colNumString = condString.substring(endIndex+1, endIndex1);
				int colNum = Integer.parseInt(colNumString);
				condExprList[a].type1 = new AttrType(AttrType.attrSymbol);
				condExprList[a].operand1.symbol = new FldSpec (new RelSpec(tableNum-1),colNum);
				int endIndex2 = condString.indexOf(" ",endIndex1+1);
				String operator = condString.substring(endIndex1+1, endIndex2);
				switch(operator){
					case "=": condExprList[a].op = new AttrOperator(AttrOperator.aopEQ);
					break;
					
					case "<": condExprList[a].op = new AttrOperator(AttrOperator.aopLT);
					break;
					
					case ">": condExprList[a].op = new AttrOperator(AttrOperator.aopGT);
					break;
					
					case "!=": condExprList[a].op = new AttrOperator(AttrOperator.aopNE);
					break;
					
					case "<=": condExprList[a].op = new AttrOperator(AttrOperator.aopLE);
					break;
					
					case ">=": condExprList[a].op = new AttrOperator(AttrOperator.aopGE);
					break;
				}
				
				//System.out.println("expr[a].op = "+condExprList[a].op);
					
				int endIndex3 = condString.indexOf(".",endIndex2);
				//System.out.println("endIndex3 = "+endIndex3);
				if(endIndex3==-1){
					
					String constantString = condString.substring(endIndex2+1);
					//System.out.println("constantString = "+constantString);
					constantString = constantString.trim();
					//System.out.println("constantString after trim() = "+constantString);
					
					System.out.println("Enter the data type of the constant in the condition\n0-> String\n 1-> Integer\n 2->Real");
					int opt  = scanner.nextInt();
					
					switch(opt){
						case 0: condExprList[a].type2 = new AttrType(AttrType.attrString);
								condExprList[a].operand2.string = constantString;
								break;
					
						case 1: condExprList[a].type2 = new AttrType(AttrType.attrInteger);
								condExprList[a].operand2.integer = Integer.parseInt(constantString);
								break;
						
						case 2: condExprList[a].type2 = new AttrType(AttrType.attrReal);
								condExprList[a].operand2.real = Float.parseFloat(constantString);
								break;
						default: System.out.println("Invalid option");
							 System.exit(0);
					}
					
					//System.out.println("expr[a].type2 = "+condExprList[a].type2);				
					
				}
				else{
					String tableNumString1 = condString.substring(endIndex2+1, endIndex3);
					int tableNum1 = Integer.parseInt(tableNumString1);
					
					String colNumString1 = condString.substring(endIndex3+1, condString.length());
					int colNum1 = Integer.parseInt(colNumString1);
					condExprList[a].type2 = new AttrType(AttrType.attrSymbol);
					condExprList[a].operand2.symbol = new FldSpec (new RelSpec(tableNum1-1),colNum1);
				}
		}
		
		
		System.out.println("Enter total memory");
		int memory = scanner.nextInt();
		
		System.out.println("Enter the number of top K tuples required in the resulting relation");
		int topK = scanner.nextInt();
		
		scanner.nextLine();
		
		System.out.println("Allow duplicates? (Y/N)");
		String dup = scanner.nextLine();
		boolean dupFlag = false;
		
		if(dup.equalsIgnoreCase("Y"))
				dupFlag = true;
			
			for(int j=0;j<numOfTables;j++){
				
				//Create attribute/column list for each table
				FldSpec [] Sprojection = new FldSpec[numOfColsList[j]];
				for(int q=0;q<Sprojection.length;q++){
				
					Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
				}
						
				Iterator am = null;
				
			    try {
			      am  = new FileScan(tableNameList[j]+".in", attrTypeList[j], stringSizesList[j], 
							  (short)numOfColsList[j], (short)numOfColsList[j],
							  Sprojection, null);
			      
			      /*Tuple t1;
					while((t1 =am.get_next())!=null){
						t1.print(attrTypeList[k]);
					}*/
								      
			    } 
			    catch (Exception e) {
				   status = false;
				   System.err.println (""+e);
				 }

				if (status != true) {
				      //bail out
				   System.err.println ("*** Error setting up scan for sailors");
				   Runtime.getRuntime().exit(1);
				}
				

			 
Iterator itr = null;
itr = new Sort(attrTypeList[j], (short)attrTypeList[j].length, stringSizesList[j],am, numOfColsList[j], new TupleOrder(TupleOrder.Descending), 4, memory );
			  	iteratorList[j] = itr;
		}	
			TopTAJoin trj = new TopTAJoin(numOfTables, attrTypeList, numOfColsList, stringSizesList, 
					joinedColList, iteratorList, indexNameList, memory, condExprList, newProjList, projlistIndex, topK, fileNames, dupFlag);
			trj.printTopKTuples();
			for(int i=0;i<numOfTables;i++)
			{
				//System.out.println("Scanned : " + trj.num_scanned(i));
			}
			for(int i=0;i<numOfTables;i++)
			{
				//System.out.println("Probed : " + trj.num_probed(i));
			}
							
		}catch(Exception e){
			e.printStackTrace();
			
			
		}finally{
			scanner.close();
		}
		System.out.println("Exit processTopTAJoin()\n");

	}
	
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		
		PhaseIITest jjoin = new PhaseIITest();
		
		//JoinsDriver2 jjoin = new JoinsDriver2();

		System.out.println("DBI Phase II");
		
		System.out.println("Enter the operation to be performed\n 1 -> TopTAJoin -> Exit ");
		Scanner scanner = new Scanner(System.in);
		
		try{
		
			int option = scanner.nextInt();
		
			switch(option){
			
			
				case 1: 
					//long readCount = jjoin.sysdef.JavabaseBM.getReadCount();
					//long writeCount = jjoin.sysdef.JavabaseBM.getWriteCount();
					//long allocateCount = jjoin.sysdef.JavabaseBM.getAllocateCount();
					//System.out.println("Before getPageAccessCount()="+jjoin.sysdef.JavabaseBM.getPageAccessCount());
					//readCount = jjoin.sysdef.JavabaseBM.getReadCount();
					//writeCount = jjoin.sysdef.JavabaseBM.getWriteCount();
					//allocateCount = jjoin.sysdef.JavabaseBM.getAllocateCount();
					long before = System.currentTimeMillis();
					processTopTAJoin();
					//System.out.println("After getPageAccessCount()="+jjoin.sysdef.JavabaseBM.getPageAccessCount());
					//readCount = jjoin.sysdef.JavabaseBM.getReadCount();
					//writeCount = jjoin.sysdef.JavabaseBM.getWriteCount();
					//allocateCount = jjoin.sysdef.JavabaseBM.getAllocateCount();
					/*System.out.println("Pages read : " + (readCount));
					System.out.println("Pages write : " + (writeCount));
					System.out.println("Pages allocated : " + (allocateCount));
					*/long after = System.currentTimeMillis();
					System.out.println("Time Taken" + (after-before)/1000 + " secs");
					break;
				case 0:
					System.out.println("Goodbye");
					break;
			}
			
			
			
		}catch(Exception e){
			
		}finally{
			scanner.close();
		}
	
	}
	
	

}