package tests;

import global.AttrOperator;
import global.AttrType;
import global.IndexType;
import global.RID;
import global.SystemDefs;
import global.ExcelParser;
import global.GlobalConst;
import global.TupleOrder;
import heap.Heapfile;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Scan;
import heap.Tuple;
import index.IndexScan;
import iterator.AdvancedSort;
import iterator.CondExpr;
import iterator.FileScan;
import iterator.FldSpec;
import iterator.Iterator;
import iterator.RelSpec;
import iterator.Sort;
import iterator.TopNRAJoinSC;
import iterator.TopNestedLoopsJoins;
import iterator.TopSortMerge;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Scanner;

import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.poifs.filesystem.POIFSFileSystem;
import org.omg.PortableInterceptor.SYSTEM_EXCEPTION;

import btree.BTreeFile;
import btree.IntegerKey;
import btree.RealKey;
import btree.StringKey;

public class PhaseIIITestSC {

	private static boolean OK = true;
	private static boolean FAIL = false;
	private static PhaseIIITestSC jjoin = null;
	SystemDefs sysdef;
	
	int numRelations;
	String [] tableNameList;
	AttrType [][] attrTypeList, updatedAttrTypeList;
	int [] numOfColsList;
	short [][] stringSizesList;
	int [] joinedColList;
	int [] joinedColDataTypeList;
	Iterator [] iteratorList;
	FldSpec[] projList;
	FileScan [] amList;
	CondExpr [] condExprList;
	int projlistIndex;
	int memory;
	int topK;
	Scanner scanner = null;
	TopNRAJoinSC sm = null;
	
	String[] fileNames = null;
	String [] indexNameList = null;	
	IndexType[] b_index = null;
	
	
	
	
	public PhaseIIITestSC() {
	    
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
 
	    //5242880, 20480,
	    
	    //sysdef = new SystemDefs( dbpath, 1000, global.GlobalConst.NUMBUF, "Clock" ); original code
	    sysdef = new SystemDefs( dbpath, 509900, 10000, "Clock" ); 
	    //sysdef = new SystemDefs( dbpath, 509900, 20480, "Clock" );
	    /*sysdef = new SystemDefs( dbpath, 509900, 1000, "Clock" ); //perfect 
	    sysdef = new SystemDefs( dbpath, 509900, 20480, "Clock" ); //perfect 509900, 20480
*/	    //sysdef = new SystemDefs( dbpath, 536870912, 20480, "Clock" );
	    
	}
	
		public void processInput(){
		
		long totalTime = 0;
		scanner = new Scanner(System.in);
		boolean status = true;
		try{
			System.out.println("Enter number of tables to be joined");
			int numOfTables = scanner.nextInt();   //2;
			numRelations = numOfTables;
			attrTypeList = new AttrType[numOfTables][];
			numOfColsList = new int[numOfTables];
			stringSizesList = new short[numOfTables][];
			joinedColList = new int[numOfTables];
			joinedColDataTypeList = new int[numOfTables]; 
			iteratorList = new Iterator[numOfTables];
			//AttrType [] indexAttrType = new AttrType[numOfTables];
			//String [] indexNameList = new String[numOfTables];
			tableNameList = new String[numOfTables];
			//ArrayList colNameList = new ArrayList();
			scanner.nextLine();
			fileNames = new String[numOfTables];
			b_index = new IndexType[numOfTables];
			indexNameList = new String[numOfTables];
			
			projList = new FldSpec[20];
		    
		    amList = new FileScan[numOfTables];
		    //projlist[1] = new FldSpec(rel, 2);
			
			projlistIndex = 0;	//Gives number of output attribute columns in the projection
			for(int k=0;k<numOfTables;k++)
			{
				boolean flag = true;
				System.out.println("Enter name for Table"+(k+1));
				String tableName = scanner.nextLine();
				tableNameList[k] = tableName;
				System.out.println("Enter file location");
				String fileLoc1 = scanner.nextLine();
				System.out.println("Enter the column number in the table to be joined (index starts with 0)");
				int joinColNumber = scanner.nextInt();
				
				joinedColList[k] = joinColNumber; 
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
																			
					col++;
					}
					
					/*for(int j=0;j<Stypes.length;j++)
						System.out.println("AttrType = "+Stypes[j].attrType);*/
					
					attrTypeList[k] = Stypes;
					
					short [] Ssizes = new short [numOfStringCol];
					for(int e=0;e<numOfStringCol;e++)
					Ssizes[e] = 30; 
					
					stringSizesList[k] = Ssizes;
					
					//Set length for the sort field i.e the field to be joined
					
					/*switch(Stypes[joinColNumber-1].attrType){
						
						case 0: joinedColDataTypeList[k] = Ssizes[0];
					        break;
					
						case 1: joinedColDataTypeList[k] = 4;
							break;
						
						case 2: joinedColDataTypeList[k] = 4;
							break;
						
						default: System.out.println("Invalid Attribute Data type");
							 System.exit(0);
					}*/
					
					//System.out.println("Data type of joined column ="+joinedColDataTypeList[k]);
					
					
					try {
						t.setHdr((short)(numOfColms),Stypes, Ssizes);
					}
					catch (Exception e) {
						System.err.println("*** error in Tuple.setHdr() ***");
						status = false;
						e.printStackTrace();
					}
		       		       
					RID rid = null;
					res = parser.splitLine();
					while (res != null && res.length!=0)
					{
						int i;
						for (i = 0; i < numOfColms; i++)
						{
							//System.out.println("Token Found [" + res[i] + "]");
							AttrType attr= Stypes[i];
							int type = attr.attrType;
							//System.out.println("type = "+type);
							switch(type){
					   			case AttrType.attrString: t.setStrFld(i+1, res[i]);
					   			//System.out.println("t.getStrFld(i+1)="+t.getStrFld(i+1));
					   				break;
					   			case AttrType.attrInteger: t.setIntFld(i+1, Integer.parseInt(res[i]));
					   				//System.out.println("t.getIntFld(i+1)="+t.getIntFld(i+1));
					   				break;
					   			case AttrType.attrReal: t.setFloFld(i+1, Float.parseFloat(res[i]));
					   				break;
							}
							//System.out.println("i =" + i);
							//System.out.println("res.length =" + res.length);
							//System.out.println("t.data = "+t.data);
															   							
						}
						if(i==Stypes.length-1){
							//System.out.println("Score =" + res[i]);
							t.setScore(Float.parseFloat(res[i]));
							t.setFloFld(i+1, Float.parseFloat(res[i]));
						}
						//System.out.println("t.data = "+t.data);
						//t.print(Stypes);
						rid = topFile.insertRecord(t.getTupleByteArray());
						//t.print(Stypes);
						res = parser.splitLine();
					}
					excelDocumentStream.close();
					
					
					
					//Create attribute/column list for each table
					FldSpec [] Sprojection = new FldSpec[numOfColms];
					for(int q=0;q<Sprojection.length;q++){
					
						Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
					}  
					
					FileScan am = null;
					
				    try {
				      am  = new FileScan(tableName+".in", Stypes, Ssizes, 
								  (short)numOfColsList[k], (short)numOfColsList[k],
								  Sprojection, null);
				      
				      /*Tuple t1;
						while((t1 =am.get_next())!=null){
							t1.print(attrTypeList[k]);
						}*/
						
				      amList[k] = am;
				      				      
						
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

		       			    
				    RelSpec rel = new RelSpec(k);
				    //int projColTableSpecificOffset= 1;
				    String moreColFlag;
				    FldSpec[] projListSpecificToTable = new FldSpec[20];
				    int projListSpecificToTableIndex=0;
				     
				    while(flag){				    	
				    	System.out.println("Enter the column number to be projected from this table");
						int colNum = scanner.nextInt();
						scanner.nextLine();
						//Set relation as outer for 1st table and as inner for 2nd table
						projList[projlistIndex] = new FldSpec(rel, colNum);
						//System.out.println("projlistIndex="+projlistIndex); 						
						System.out.println("Are there more columns to be projected from this table (Y/N)?");
						moreColFlag = scanner.nextLine();
						
						if(moreColFlag.equalsIgnoreCase("Y"))
							flag=true;
						else if(moreColFlag.equalsIgnoreCase("N"))
							flag=false;
						projlistIndex++;
				    }			        
				    
			  }
		      catch(Exception e)
		      {
		        e.printStackTrace();
		      }

			  	
			//EOC
		    //scanner.nextLine();
		    
		}
		//System.out.println("projlistIndex ="+projlistIndex);
		/*System.out.println("Enter the number of conditions in the where clause ");
				
		int numCondExpr = scanner.nextInt();
		scanner.nextLine();
		String [] conditionString = new String[numCondExpr];
		for(int a=0; a<numCondExpr ; a++)
		{
			System.out.println("Enter the "+(a+1)+" condition in the following format\n" + 
					"<**TableNumber**>.<**ColumnNumber**> <**operator**> <**TableNumber**>.<**ColumnNumber**>/<**Constant**> ");
			conditionString[a] = scanner.nextLine();
				
		}
		for(int a=0; a<numCondExpr ; a++){
				
			System.out.println(conditionString[a]);
			if(a!=numCondExpr-1){
				System.out.println("AND");
			}
		}
		
	
		condExprList = new CondExpr[numCondExpr+1];
		//System.out.println("expr.length ="+condExprList.length);
		
		for(int a=0;a<condExprList.length-1;a++){
			
				//System.out.println("condString =");
				condExprList[a] = new CondExpr();
				String condString = conditionString[a];
				condExprList[a].next  = null;
				//System.out.println("condString ="+condString);
				//System.out.println("a ="+a);
				int beginIndex = 0;
				int endIndex = condString.indexOf(".", 0);
				//System.out.println("endIndex ="+endIndex);
				//char tableNum=condString.charAt(index-1);
				String tableNumString = condString.substring(beginIndex, endIndex);
				//System.out.println("tableNumString ="+tableNumString);
				int tableNum = Integer.parseInt(tableNumString);
				//System.out.println("tableNum ="+tableNum);
				//String tableName = tableNameList[tableNum-1];
				int endIndex1 = condString.indexOf(" ",endIndex);
				//System.out.println("endIndex1 ="+endIndex1);
				String colNumString = condString.substring(endIndex+1, endIndex1);
				//System.out.println("colNumString ="+colNumString);
				int colNum = Integer.parseInt(colNumString);
				//System.out.println("colNum ="+colNum);
				
				condExprList[a].type1 = new AttrType(AttrType.attrSymbol);
				
				//Set relation as outer for 1st table and as inner for 2nd table
				RelSpec rel1 = null;
				if(tableNum==0){
					rel1 = new RelSpec(RelSpec.outer);
				}
				else{
					rel1 = new RelSpec(RelSpec.innerRel);
				}
								
				condExprList[a].operand1.symbol = new FldSpec (rel1,colNum);
								
				int endIndex2 = condString.indexOf(" ",endIndex1+1);
				//System.out.println("endIndex2 ="+endIndex2);
				String operator = condString.substring(endIndex1+1, endIndex2);
				//System.out.println("operator = "+operator);
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
					//System.out.println("tableNumString1 = "+tableNumString1);
					int tableNum1 = Integer.parseInt(tableNumString1);
					//System.out.println("tableNum1 = "+tableNum1);
					//String tableName = tableNameList[tableNum-1];
					
					//int endIndex4 = condString.indexOf(" ",endIndex3);
					String colNumString1 = condString.substring(endIndex3+1, condString.length());
					int colNum1 = Integer.parseInt(colNumString1);
					//System.out.println("colNum1 = "+colNum1);
					//attr = attrTypeList[tableNum1-1][colNum1-1];
					//expr[a].type2 = new AttrType(attr.attrType);
					condExprList[a].type2 = new AttrType(AttrType.attrSymbol);
					//System.out.println("expr[a].type2 = "+condExprList[a].type2);
					
					RelSpec rel2 = null;
					if(tableNum1==0){
						rel2 = new RelSpec(RelSpec.outer);
					}
					else{
						rel2 = new RelSpec(RelSpec.innerRel);
					}
									
					condExprList[a].operand2.symbol = new FldSpec (rel2,colNum1);
					//System.out.println("expr[a].operand2.symbol = "+condExprList[a].operand2.symbol);
				}
		}
		
		condExprList[condExprList.length-1] = null; */
		
		System.out.println("Enter total memory");
		memory = scanner.nextInt();
		
		System.out.println("Enter the number of top K tuples required in the resulting relation");
		topK = scanner.nextInt();
		
		scanner.nextLine();
		
		for(int j=0;j<numRelations;j++){
			
				//Create attribute/column list for each table
				FldSpec [] Sprojection = new FldSpec[numOfColsList[j]];
				for(int q=0;q<Sprojection.length;q++){
				
					Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
				}
						
				FileScan am = null;
				
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
				   System.err.println ("*** Error setting up scan");
				   Runtime.getRuntime().exit(1);
				}
				
			   /* DuplElim ed = null;
			    Tuple t2 = new Tuple();
			    t2 = null;
			    try {
			      ed = new DuplElim(attrTypeList[j], (short)numOfColsList[j], stringSizesList[j], am, memory, false);
			    }
			    catch (Exception e) {
			      System.err.println (""+e);
			      Runtime.getRuntime().exit(1);
			    }*/
			 
			    //QueryCheck qcheck4 = new QueryCheck(4);
	
			    
			   // t2 = null;
			 
			    /*try {
			      while ((t2 = ed.get_next()) != null) {
			        t2.print(attrTypeList[j]);
			        System.out.println("t2.getScore()"+t2.getScore());
			        qcheck4.Check(t2);
			      }
			    }
			    catch (Exception e) {
			      System.err.println (""+e);
			      e.printStackTrace(); 
			      Runtime.getRuntime().exit(1);
			      }*/
			    
			   /* qcheck4.report(4);
			    try {
			      ed.close();
			    }
			    catch (Exception e) {
			      status = FAIL;
			      e.printStackTrace();*/
				Iterator itr = null;
				itr = new AdvancedSort(attrTypeList[j], (short)attrTypeList[j].length, stringSizesList[j],am, numOfColsList[j], 
								new TupleOrder(TupleOrder.Descending), 4, memory);
			  	iteratorList[j] = itr;
			  	Tuple t1;
			  	/*System.out.println("in phase 3");
				while((t1 =itr.get_next())!=null){
					t1.print(attrTypeList[j]);
				}
				System.out.println("in phase 3 end ");*/
				
			  	
			}	
		
		}catch(Exception e){
			
			e.printStackTrace();
			
		}/*finally{
			scanner.close();
		}*/
			
	}
	
	public void createInput(){
		
		long totalTime = 0;
		scanner = new Scanner(System.in);
		boolean status = true;
		
		try{
			//System.out.println("Enter number of tables to be joined");
			int numOfTables = 2;
			numRelations = numOfTables;
			attrTypeList = new AttrType[numOfTables][];
			numOfColsList = new int[numOfTables];
			stringSizesList = new short[numOfTables][];
			joinedColList = new int[numOfTables];
			joinedColDataTypeList = new int[numOfTables]; 
			iteratorList = new Iterator[numOfTables];
			//AttrType [] indexAttrType = new AttrType[numOfTables];
			//String [] indexNameList = new String[numOfTables];
			tableNameList = new String[numOfTables];
			//ArrayList colNameList = new ArrayList();
			//scanner.nextLine();
		
			fileNames = new String[numOfTables];
			b_index = new IndexType[numOfTables];
			indexNameList = new String[numOfTables];
			
			
			projList = new FldSpec[20];
		    
		    amList = new FileScan[numOfTables];
		    //projlist[1] = new FldSpec(rel, 2);
			
			projlistIndex = 0;	//Gives number of output attribute columns in the projection
			//for(int k=0;k<numOfTables;k++)
			//{
				boolean flag = true;
				//System.out.println("Enter name for Table"+(k+1));
				//String tableName = scanner.nextLine();
				tableNameList[0] = "ExcelTest1";
				tableNameList[1] = "ExcelTest3";
				//System.out.println("Enter file location");
				String fileLoc1 = "C:\\data\\ExcelTest1.xls";
				String fileLoc2 = "C:\\data\\ExcelTest3.xls";			
				//System.out.println("Enter the column number in the table to be joined");
				//int joinColNumber = scanner.nextInt();
				
				joinedColList[0] = 0; 
				joinedColList[1] = 0;
				numOfColsList[0] = 4;
				numOfColsList[1] = 4;
				//SOC
				HSSFWorkbook workBook = null; 
				File file1  = new File(fileLoc1);
				File file2  = new File(fileLoc2);
				InputStream excelDocumentStream = null;
				try 
				{
					excelDocumentStream = new FileInputStream(file1);
					POIFSFileSystem fsPOI = new POIFSFileSystem(new BufferedInputStream(excelDocumentStream));
					workBook = new HSSFWorkbook(fsPOI);         
					ExcelParser parser = new ExcelParser(workBook.getSheetAt(0));
					String [] res;
		       		       
					Heapfile topFile = new Heapfile(tableNameList[0]+".in");
						       
					Tuple t = new Tuple();
					
					AttrType [] Stypes1 = new AttrType[numOfColsList[0]];
					int col=0;
					
					Stypes1[0] = new AttrType(AttrType.attrString);
					Stypes1[1] = new AttrType(AttrType.attrInteger);
					Stypes1[2] = new AttrType(AttrType.attrString);
					Stypes1[3] = new AttrType(AttrType.attrReal);
					
					int numOfStringCol1 = 2;
					
					
					attrTypeList[0] = Stypes1;
					//attrTypeList[1] = Stypes2;
					
					short [] Ssizes1 = new short [numOfStringCol1];
					for(int e=0;e<numOfStringCol1;e++)
					Ssizes1[e] = 30;
					
					/*short [] Ssizes2 = new short [numOfStringCol2];
					for(int e=0;e<numOfStringCol2;e++)
					Ssizes2[e] = 30;*/ 
					
					stringSizesList[0] = Ssizes1;
					
					//Set length for the sort field i.e the field to be joined
					/*removed old switch case and 
					 * switch(Stypes1[joinedColList[0]-1].attrType){ to switch(Stypes1[joinedColList[0]].attrType){
					 * LOOKS LIKE THIS BLOCK IS NOT REQUIRED   
					 */
				
					switch(Stypes1[joinedColList[0]].attrType){
						
						case 0: joinedColDataTypeList[0] = Ssizes1[0];
					        break;
					
						case 1: joinedColDataTypeList[0] = 4;
							break;
						
						case 2: joinedColDataTypeList[0] = 4;
							break;
						
						default: System.out.println("Invalid Attribute Data type");
							 System.exit(0);
					}
					
					//System.out.println("Data type of joined column ="+joinedColDataTypeList[k]);
					
					
					try {
						t.setHdr((short)(numOfColsList[0]),Stypes1, Ssizes1);
					}
					catch (Exception e) {
						System.err.println("*** error in Tuple.setHdr() ***");
						status = false;
						e.printStackTrace();
					}
		       		       
					RID rid = null;
					res = parser.splitLine();
					while (res != null && res.length!=0)
					{
						int i;
						for (i = 0; i < numOfColsList[0]; i++)
						{
							//System.out.println("Token Found [" + res[i] + "]");
							AttrType attr= Stypes1[i];
							int type = attr.attrType;
							//System.out.println("type = "+type);
							switch(type){
					   			case AttrType.attrString: t.setStrFld(i+1, res[i]);
					   			//System.out.println("t.getStrFld(i+1)="+t.getStrFld(i+1));
					   				break;
					   			case AttrType.attrInteger: t.setIntFld(i+1, Integer.parseInt(res[i]));
					   				//System.out.println("t.getIntFld(i+1)="+t.getIntFld(i+1));
					   				break;
					   			case AttrType.attrReal: t.setFloFld(i+1, Float.parseFloat(res[i]));
					   				break;
							}
							//System.out.println("i =" + i);
							//System.out.println("res.length =" + res.length);
							//System.out.println("t.data = "+t.data);
															   							
						}
						if(i==Stypes1.length-1){
							//System.out.println("Score =" + res[i]);
							t.setScore(Float.parseFloat(res[i]));
							t.setFloFld(i+1, Float.parseFloat(res[i]));
						}
						//System.out.println("t.data = "+t.data);
						//t.print(Stypes);
						rid = topFile.insertRecord(t.getTupleByteArray());
						//t.print(Stypes);
						res = parser.splitLine();
					}
					excelDocumentStream.close();
					
					// create an scan on the heapfile
					/*Scan scan = null;
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
						btf = new BTreeFile(tableNameList[0]+"_BTreeIndex", attrTypeList[0][joinedColList[0]].attrType, GlobalConst.INDEX_REC_LEN, 1); 
						indexNameList[0] = tableNameList[0]+"_BTreeIndex";
						b_index[0] = new IndexType(IndexType.B_Index);
						fileNames[0] = tableNameList[0]+".in";
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
							switch(attrTypeList[0][joinedColList[0]].attrType){
							case AttrType.attrString: String keyString = t.getStrFld(joinedColList[0]+1);
							btf.insert(new StringKey(keyString), rid1); 
							break;
							case AttrType.attrInteger: int keyInt = t.getIntFld(joinedColList[0]+1);
							btf.insert(new IntegerKey(keyInt), rid1); 
							break;
							case AttrType.attrReal: float keyFloat = t.getFloFld(joinedColList[0]+1);
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
					btf.close();

					System.out.println("BTreeIndex file created successfully.\n"); */
					
					//Create attribute/column list for each table
					FldSpec [] Sprojection = new FldSpec[numOfColsList[0]];
					for(int q=0;q<Sprojection.length;q++){
					
						Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
					}  
					
					FileScan am = null;
					
				    try {
				      am  = new FileScan(tableNameList[0]+".in", Stypes1, Ssizes1, 
								  (short)numOfColsList[0], (short)numOfColsList[0],
								  Sprojection, null);
				      
				      /*Tuple t1;
						while((t1 =am.get_next())!=null){
							t1.print(attrTypeList[k]);
						}*/
						
				      amList[0] = am;
				      				      
						
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

		       			    
				    RelSpec rel = new RelSpec(0);
				    //int projColTableSpecificOffset= 1;
				    String moreColFlag;
				    
				     
				    while(flag){				    	
				    	System.out.println("Enter the column number to be projected from this table");
						int colNum = scanner.nextInt();
						scanner.nextLine();
						//Set relation as outer for 1st table and as inner for 2nd table
						
						projList[projlistIndex] = new FldSpec(rel, colNum);
						//System.out.println("projlistIndex="+projlistIndex); 
						
						System.out.println("Are there more columns to be projected from this table (Y/N)?");
						moreColFlag = scanner.nextLine();
						
						if(moreColFlag.equalsIgnoreCase("Y"))
							flag=true;
						else if(moreColFlag.equalsIgnoreCase("N"))
							flag=false;
						projlistIndex++;
				    }			        
				    
			  }
		      catch(Exception e)
		      {
		        e.printStackTrace();
		      }
				flag=true;
		 
				try 
				{
					excelDocumentStream = new FileInputStream(file2);
					POIFSFileSystem fsPOI = new POIFSFileSystem(new BufferedInputStream(excelDocumentStream));
					workBook = new HSSFWorkbook(fsPOI);         
					ExcelParser parser = new ExcelParser(workBook.getSheetAt(0));
					String [] res;
		       		       
					Heapfile topFile = new Heapfile(tableNameList[1]+".in");
						       
					Tuple t = new Tuple();
					
					AttrType [] Stypes1 = new AttrType[numOfColsList[1]];
					int col=0;
					
					Stypes1[0] = new AttrType(AttrType.attrString);
					Stypes1[1] = new AttrType(AttrType.attrInteger);
					Stypes1[2] = new AttrType(AttrType.attrString);
					Stypes1[3] = new AttrType(AttrType.attrReal);
					
					int numOfStringCol1 = 2;
					
					
					attrTypeList[1] = Stypes1;
					//attrTypeList[1] = Stypes2;
					
					short [] Ssizes1 = new short [numOfStringCol1];
					for(int e=0;e<numOfStringCol1;e++)
					Ssizes1[e] = 30;
					
					stringSizesList[1]=Ssizes1;
					
					//Set length for the sort field i.e the field to be joined
					
					switch(Stypes1[joinedColList[1]].attrType){
						
						case 0: joinedColDataTypeList[1] = Ssizes1[0];
					        break;
					
						case 1: joinedColDataTypeList[1] = 4;
							break;
						
						case 2: joinedColDataTypeList[1] = 4;
							break;
						
						default: System.out.println("Invalid Attribute Data type");
							 System.exit(0);
					}
					
					//System.out.println("Data type of joined column ="+joinedColDataTypeList[k]);
					
					try {
						t.setHdr((short)(numOfColsList[1]),Stypes1, Ssizes1);
					}
					catch (Exception e) {
						System.err.println("*** error in Tuple.setHdr() ***");
						status = false;
						e.printStackTrace();
					}
					
					
					RID rid = null;
					res = parser.splitLine();
					while (res != null && res.length!=0)
					{
						int i;
						for (i = 0; i < numOfColsList[1]; i++)
						{
							//System.out.println("Token Found [" + res[i] + "]");
							AttrType attr= Stypes1[i];
							int type = attr.attrType;
							//System.out.println("type = "+type);
							switch(type){
					   			case AttrType.attrString: t.setStrFld(i+1, res[i]);
					   			//System.out.println("t.getStrFld(i+1)="+t.getStrFld(i+1));
					   				break;
					   			case AttrType.attrInteger: t.setIntFld(i+1, Integer.parseInt(res[i]));
					   				//System.out.println("t.getIntFld(i+1)="+t.getIntFld(i+1));
					   				break;
					   			case AttrType.attrReal: t.setFloFld(i+1, Float.parseFloat(res[i]));
					   				break;
							}
							//System.out.println("i =" + i);
							//System.out.println("res.length =" + res.length);
							//System.out.println("t.data = "+t.data);
															   							
						}
						if(i==Stypes1.length-1){
							//System.out.println("Score =" + res[i]);
							t.setScore(Float.parseFloat(res[i]));
							t.setFloFld(i+1, Float.parseFloat(res[i]));
						}
						//System.out.println("t.data = "+t.data);
						//t.print(Stypes);
						rid = topFile.insertRecord(t.getTupleByteArray());
						//t.print(Stypes);
						res = parser.splitLine();
					}
					excelDocumentStream.close();
					
					/*
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
						btf = new BTreeFile(tableNameList[1]+"_BTreeIndex", attrTypeList[1][joinedColList[1]].attrType, GlobalConst.INDEX_REC_LEN, 1delete); 
						indexNameList[1] = tableNameList[1]+"_BTreeIndex";
						b_index[1] = new IndexType(IndexType.B_Index);
						fileNames[1] = tableNameList[1]+".in";
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
							switch(attrTypeList[1][joinedColList[1]].attrType){
							case AttrType.attrString: String keyString = t.getStrFld(joinedColList[1]+1);
							btf.insert(new StringKey(keyString), rid1); 
							break;
							case AttrType.attrInteger: int keyInt = t.getIntFld(joinedColList[1]+1);
							btf.insert(new IntegerKey(keyInt), rid1); 
							break;
							case AttrType.attrReal: float keyFloat = t.getFloFld(joinedColList[1]+1);
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
					btf.close();

					System.out.println("BTreeIndex file created successfully.\n"); */
					
					//Create attribute/column list for each table
					FldSpec [] Sprojection = new FldSpec[numOfColsList[1]];
					for(int q=0;q<Sprojection.length;q++){
					
						Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
					}  
					
					FileScan am = null;
					
				    try {
				      am  = new FileScan(tableNameList[1]+".in", Stypes1, Ssizes1, 
								  (short)numOfColsList[1], (short)numOfColsList[1],
								  Sprojection, null);
				      
				      /*Tuple t1;
						while((t1 =am.get_next())!=null){
							t1.print(attrTypeList[k]);
						}*/
						
				      amList[1] = am;				      				      
						
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

		       			    
				    RelSpec rel = new RelSpec(1);
				    //int projColTableSpecificOffset= 1;
				    String moreColFlag;
				    
				     
				    while(flag){				    	
				    	System.out.println("Enter the column number to be projected from this table");
						int colNum = scanner.nextInt();
						scanner.nextLine();
						projList[projlistIndex] = new FldSpec(rel, colNum);
						//System.out.println("projlistIndex="+projlistIndex); 
						
						System.out.println("Are there more columns to be projected from this table (Y/N)?");
						moreColFlag = scanner.nextLine();
						
						if(moreColFlag.equalsIgnoreCase("Y"))
							flag=true;
						else if(moreColFlag.equalsIgnoreCase("N"))
							flag=false;
						projlistIndex++;
				    }
				    scanner.nextLine();
				    
			  }
		      catch(Exception e)
		      {
		        e.printStackTrace();
		      }	
			
		    
		//}
		//System.out.println("projlistIndex ="+projlistIndex);
				condExprList = null;
		/*System.out.println("Enter the number of conditions in the where clause ");
				
		int numCondExpr = scanner.nextInt();
		scanner.nextLine();
		String [] conditionString = new String[numCondExpr];
		for(int a=0; a<numCondExpr ; a++)
		{
			System.out.println("Enter the "+(a+1)+" condition in the following format\n" + 
					"<**TableNumber**>.<**ColumnNumber**> <**operator**> <**TableNumber**>.<**ColumnNumber**>/<**Constant**> ");
			conditionString[a] = scanner.nextLine();
				
		}
		for(int a=0; a<numCondExpr ; a++){
				
			System.out.println(conditionString[a]);
			if(a!=numCondExpr-1){
				System.out.println("AND");
			}
		}
		
	
		condExprList = new CondExpr[numCondExpr+1];
		//System.out.println("expr.length ="+condExprList.length);
		
		for(int a=0;a<condExprList.length-1;a++){
			
				//System.out.println("condString =");
				condExprList[a] = new CondExpr();
				String condString = conditionString[a];
				condExprList[a].next  = null;
				//System.out.println("condString ="+condString);
				//System.out.println("a ="+a);
				int beginIndex = 0;
				int endIndex = condString.indexOf(".", 0);
				//System.out.println("endIndex ="+endIndex);
				//char tableNum=condString.charAt(index-1);
				String tableNumString = condString.substring(beginIndex, endIndex);
				//System.out.println("tableNumString ="+tableNumString);
				int tableNum = Integer.parseInt(tableNumString);
				//System.out.println("tableNum ="+tableNum);
				//String tableName = tableNameList[tableNum-1];
				int endIndex1 = condString.indexOf(" ",endIndex);
				//System.out.println("endIndex1 ="+endIndex1);
				String colNumString = condString.substring(endIndex+1, endIndex1);
				//System.out.println("colNumString ="+colNumString);
				int colNum = Integer.parseInt(colNumString);
				//System.out.println("colNum ="+colNum);
				
				condExprList[a].type1 = new AttrType(AttrType.attrSymbol);
				
				//Set relation as outer for 1st table and as inner for 2nd table
				RelSpec rel1 = null;
				if(tableNum==0){
					rel1 = new RelSpec(RelSpec.outer);
				}
				else{
					rel1 = new RelSpec(RelSpec.innerRel);
				}
								
				condExprList[a].operand1.symbol = new FldSpec (rel1,colNum);
								
				int endIndex2 = condString.indexOf(" ",endIndex1+1);
				//System.out.println("endIndex2 ="+endIndex2);
				String operator = condString.substring(endIndex1+1, endIndex2);
				//System.out.println("operator = "+operator);
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
					//System.out.println("tableNumString1 = "+tableNumString1);
					int tableNum1 = Integer.parseInt(tableNumString1);
					//System.out.println("tableNum1 = "+tableNum1);
					//String tableName = tableNameList[tableNum-1];
					
					//int endIndex4 = condString.indexOf(" ",endIndex3);
					String colNumString1 = condString.substring(endIndex3+1, condString.length());
					int colNum1 = Integer.parseInt(colNumString1);
					//System.out.println("colNum1 = "+colNum1);
					//attr = attrTypeList[tableNum1-1][colNum1-1];
					//expr[a].type2 = new AttrType(attr.attrType);
					condExprList[a].type2 = new AttrType(AttrType.attrSymbol);
					//System.out.println("expr[a].type2 = "+condExprList[a].type2);
					
					RelSpec rel2 = null;
					if(tableNum1==0){
						rel2 = new RelSpec(RelSpec.outer);
					}
					else{
						rel2 = new RelSpec(RelSpec.innerRel);
					}
									
					condExprList[a].operand2.symbol = new FldSpec (rel2,colNum1);
					//System.out.println("expr[a].operand2.symbol = "+condExprList[a].operand2.symbol);
				}
		}
		
		condExprList[condExprList.length-1] = null; */
		
		//System.out.println("Enter total memory");
		memory = 10;
		
		//System.out.println("Enter the number of top K tuples required in the resulting relation");
		topK = 4;
		
		//scanner.nextLine();
		
		for(int j=0;j<numRelations;j++){
			
				//Create attribute/column list for each table
				FldSpec [] Sprojection = new FldSpec[numOfColsList[j]];
				for(int q=0;q<Sprojection.length;q++){
				
					Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
				}
						
				FileScan am = null;
				
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
				   System.err.println ("*** Error setting up scan");
				   Runtime.getRuntime().exit(1);
				}
				
			   /* DuplElim ed = null;
			    Tuple t2 = new Tuple();
			    t2 = null;
			    try {
			      ed = new DuplElim(attrTypeList[j], (short)numOfColsList[j], stringSizesList[j], am, memory, false);
			    }
			    catch (Exception e) {
			      System.err.println (""+e);
			      Runtime.getRuntime().exit(1);
			    }*/
			 
			    //QueryCheck qcheck4 = new QueryCheck(4);
	
			    
			   // t2 = null;
			 
			    /*try {
			      while ((t2 = ed.get_next()) != null) {
			        t2.print(attrTypeList[j]);
			        System.out.println("t2.getScore()"+t2.getScore());
			        qcheck4.Check(t2);
			      }
			    }
			    catch (Exception e) {
			      System.err.println (""+e);
			      e.printStackTrace(); 
			      Runtime.getRuntime().exit(1);
			      }*/
			    
			   /* qcheck4.report(4);
			    try {
			      ed.close();
			    }
			    catch (Exception e) {
			      status = FAIL;
			      e.printStackTrace();*/
				Iterator itr = null;
				itr = new AdvancedSort(attrTypeList[j], (short)attrTypeList[j].length, stringSizesList[j],am, numOfColsList[j], 
								new TupleOrder(TupleOrder.Descending), 4, memory);
			  	iteratorList[j] = itr;
			  	Tuple t1;
			  	/*System.out.println("in phase 3");
				while((t1 =itr.get_next())!=null){
					t1.print(attrTypeList[j]);
				}
				System.out.println("in phase 3 end ");*/
				
			  	
			}	
		
		}catch(Exception e){
			
			e.printStackTrace();
			
		}/*finally{
			scanner.close();
		}*/
			
	}
	
	public void processTopNRAJoin(){
		
		long readCount = jjoin.sysdef.JavabaseBM.getReadCount();
		long writeCount = jjoin.sysdef.JavabaseBM.getWriteCount();
		//long allocateCount = jjoin.sysdef.JavabaseBM.getAllocateCount();
		processInput();
		//createInput();
		long totalTime = 0;
		boolean status = true;
		try {
    		
    		/*System.out.println("attrTypeList = "+attrTypeList.length);
    		for(int i=0;i<attrTypeList.length;i++)
    		for(int j=0;j<attrTypeList[i].length;j++)
    			System.out.println("AttrType = "+attrTypeList[i][j].attrType);*/
    		updatedAttrTypeList = new AttrType[numRelations][];   
    		
    		for(int i=0;i<attrTypeList.length;i++){
    			int attrIndex = 0;
    			AttrType[] interAttr = new AttrType[attrTypeList[i].length+1];
    			for(int j=0;j<attrTypeList[i].length;j++){
    				interAttr[attrIndex++] = attrTypeList[i][j];
    			}
    			//these two are added to store best score and worst score
        		interAttr[attrIndex]= new AttrType(AttrType.attrInteger);
    			updatedAttrTypeList[i] = interAttr;
    			//interAttr[attrIndex++]= new AttrType(AttrType.attrReal);
    		}
    		
    		long start = System.currentTimeMillis();
	        sm = new TopNRAJoinSC(numRelations, updatedAttrTypeList, numOfColsList, stringSizesList, joinedColList, iteratorList, memory,
	        		condExprList, projList, projlistIndex, topK, tableNameList,indexNameList );
    		long finish = System.currentTimeMillis();
    		totalTime = finish - start;
    		System.out.println("totaltime ="+totalTime);
    		System.out.println("Pages read : " + (jjoin.sysdef.JavabaseBM.getReadCount() - readCount));
			System.out.println("Pages write : " + (jjoin.sysdef.JavabaseBM.getWriteCount() - writeCount));
			
	    }
	    catch (Exception e) {
	      System.err.println("*** join error in TopNRAJoin constructor ***"); 
	      status = false;
	      System.err.println (""+e);
	      e.printStackTrace();
	    }
				
	}
	
	
	public void addRecords(){
		
		
		scanner = new Scanner(System.in);
		Iterator itr = null;
		ArrayList itrList = new ArrayList();
		int tableIndex=-1;
		ArrayList relationList = new ArrayList();
		ArrayList<String> relationNames = new ArrayList<String>();
		while(true){
		//int numOfTables = scanner.nextInt();   //2;
		
		System.out.println("Enter the index of the table to be updated");
		for(int i=0;i<tableNameList.length;i++){
			System.out.println("Index : "+i+"\t for "+tableNameList[i]);
		}
		
		//String tableName = scanner.next();
		tableIndex= scanner.nextInt();
		//String tableName = "ExcelTest1";
		if(tableNameList==null){
			System.out.println("Tables do not exist");
			System.exit(0);
		}
		
		/*for(int i=0;i<tableNameList.length;i++){
			if(tableNameList[i].equalsIgnoreCase(tableName)){
				tableIndex = i;
				break;
			}
		}*/
		if(tableIndex<0){
			
			System.out.println("Table not found");
			System.exit(0);
		}
		else{
			relationList.add(tableIndex);
			Tuple t = new Tuple();
			try {
				t.setHdr((short)(numOfColsList[tableIndex]),attrTypeList[tableIndex], stringSizesList[tableIndex]);
			} catch (InvalidTypeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InvalidTupleSizeException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}catch(Exception e){
				e.printStackTrace();
			}
			scanner.nextLine();
			System.out.println("Enter the name of the file with update data");
			String updatedFileName = scanner.nextLine();
			//String updatedFileName = "eUp";
			/*System.out.println("Enter file location");
			String fileLoc = scanner.nextLine();*/
			String fileLoc = "C://data//"+updatedFileName+".xls";
			//String fileLoc = "C://data//eUp.xls";
			
			HSSFWorkbook workBook = null; 
			File file  = new File(fileLoc);
			InputStream excelDocumentStream = null;
			try 
			{
				excelDocumentStream = new FileInputStream(file);
				POIFSFileSystem fsPOI = new POIFSFileSystem(new BufferedInputStream(excelDocumentStream));
				workBook = new HSSFWorkbook(fsPOI);         
				ExcelParser parser = new ExcelParser(workBook.getSheetAt(0));
				String [] res;
	       		relationNames.add(updatedFileName);
				Heapfile topFile = new Heapfile(updatedFileName+".in");
					       
				//t = new Tuple();

				RID rid = null;
				res = parser.splitLine();
				while (res != null && res.length!=0)
				{
					int i;
					for (i = 0; i < numOfColsList[tableIndex]; i++)
					{
						//System.out.println("Token Found [" + res[i] + "]");
						AttrType attr= attrTypeList[tableIndex][i];
						int type = attr.attrType;
						//System.out.println("type = "+type);
						switch(type){
				   			case AttrType.attrString: t.setStrFld(i+1, res[i]);
				   			//System.out.println("t.getStrFld(i+1)="+t.getStrFld(i+1));
				   				break;
				   			case AttrType.attrInteger: t.setIntFld(i+1, Integer.parseInt(res[i]));
				   				//System.out.println("t.getIntFld(i+1)="+t.getIntFld(i+1));
				   				break;
				   			case AttrType.attrReal: t.setFloFld(i+1, Float.parseFloat(res[i]));
				   				break;
						}
						//System.out.println("i =" + i);
						//System.out.println("res.length =" + res.length);
						//System.out.println("t.data = "+t.data);
														   							
					}
					if(i==attrTypeList[tableIndex].length-1){
						//System.out.println("Score =" + res[i]);
						t.setScore(Float.parseFloat(res[i]));
						t.setFloFld(i+1, Float.parseFloat(res[i]));
					}
					//System.out.println("t.data = "+t.data);
					//t.print(Stypes);
					rid = topFile.insertRecord(t.getTupleByteArray());
					//t.print(Stypes);
					res = parser.splitLine();
				}
				excelDocumentStream.close();
				
				//Create attribute/column list for each table
				FldSpec [] Sprojection = new FldSpec[numOfColsList[tableIndex]];
				for(int q=0;q<Sprojection.length;q++){
				
					Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
				}  
				
				FileScan am = null;
				
			    try {
			      am  = new FileScan(updatedFileName+".in", attrTypeList[tableIndex], stringSizesList[tableIndex], 
							  (short)numOfColsList[tableIndex], (short)numOfColsList[tableIndex],
							  Sprojection, null);
			      
			      	
					
				itr = null;
				itr = new AdvancedSort(attrTypeList[tableIndex], (short)attrTypeList[tableIndex].length, stringSizesList[tableIndex],am, numOfColsList[tableIndex], 
								new TupleOrder(TupleOrder.Descending), 4, memory);
				
				/*Tuple t1;
				while((t1 =itr.get_next())!=null){
					t1.print(updatedAttrTypeList[tableIndex]);
				}*/	
					
			      //sm.AddTopNRAJoin(itr,tableIndex);
					
			    }
			    catch (Exception e) {
			     System.err.println (""+e);
			    }

			    
			}catch(Exception e){
				e.printStackTrace();
			}
			
			itrList.add(itr);
			
		}
		
		System.out.println("Are there more files to be updated? (Y/N)");
		String flag = scanner.nextLine();
		if(flag.equalsIgnoreCase("N"))
			break;
		}
		try {
			sm.AddTopNRAJoin(itrList,relationList,relationNames);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}		
	}
	
	public void deleteRecords(){
		scanner = new Scanner(System.in);
		//int numOfTables = scanner.nextInt();   //2;
		
		/*System.out.println("Enter the name of the table to be updated");
		String tableName = scanner.next();*/
		String tableName = "ExcelTest1";
		if(tableNameList==null){
			System.out.println("Tables do not exist");
			System.exit(0);
		}
		int tableIndex=-1;
		for(int i=0;i<tableNameList.length;i++){
			if(tableNameList[i].equalsIgnoreCase(tableName)){
				tableIndex = i;
				break;
			}
		}
		if(tableIndex<0){
			
			System.out.println("Table not found");
			System.exit(0);
		}
		else{
			
			Tuple t = new Tuple();
			try {
				t.setHdr((short)(numOfColsList[tableIndex]),attrTypeList[tableIndex], stringSizesList[tableIndex]);
			} catch(Exception e){
				e.printStackTrace();
			}
			scanner.nextLine();
			/*System.out.println("Enter the name of the updated file");
			String updatedFileName = scanner.nextLine();*/
			String updatedFileName = "e1up";
			/*System.out.println("Enter file location");
			String fileLoc = scanner.nextLine();*/
			String fileLoc = "C://data//e1up.xls";
			
			HSSFWorkbook workBook = null; 
			File file  = new File(fileLoc);
			InputStream excelDocumentStream = null;
			try 
			{
				excelDocumentStream = new FileInputStream(file);
				POIFSFileSystem fsPOI = new POIFSFileSystem(new BufferedInputStream(excelDocumentStream));
				workBook = new HSSFWorkbook(fsPOI);         
				ExcelParser parser = new ExcelParser(workBook.getSheetAt(0));
				String [] res;
	       		       
				Heapfile topFile = new Heapfile(updatedFileName+".in");
					       
				//t = new Tuple();

				RID rid = null;
				res = parser.splitLine();
				while (res != null && res.length!=0)
				{
					int i;
					for (i = 0; i < numOfColsList[tableIndex]; i++)
					{
						//System.out.println("Token Found [" + res[i] + "]");
						AttrType attr= attrTypeList[tableIndex][i];
						int type = attr.attrType;
						//System.out.println("type = "+type);
						switch(type){
				   			case AttrType.attrString: t.setStrFld(i+1, res[i]);
				   			//System.out.println("t.getStrFld(i+1)="+t.getStrFld(i+1));
				   				break;
				   			case AttrType.attrInteger: t.setIntFld(i+1, Integer.parseInt(res[i]));
				   				//System.out.println("t.getIntFld(i+1)="+t.getIntFld(i+1));
				   				break;
				   			case AttrType.attrReal: t.setFloFld(i+1, Float.parseFloat(res[i]));
				   				break;
						}
						//System.out.println("i =" + i);
						//System.out.println("res.length =" + res.length);
						//System.out.println("t.data = "+t.data);
														   							
					}
					if(i==attrTypeList[tableIndex].length-1){
						//System.out.println("Score =" + res[i]);
						t.setScore(Float.parseFloat(res[i]));
						t.setFloFld(i+1, Float.parseFloat(res[i]));
					}
					//System.out.println("t.data = "+t.data);
					//t.print(Stypes);
					rid = topFile.insertRecord(t.getTupleByteArray());
					//t.print(Stypes);
					res = parser.splitLine();
				}
				excelDocumentStream.close();
				
				//Create attribute/column list for each table
				FldSpec [] Sprojection = new FldSpec[numOfColsList[tableIndex]];
				for(int q=0;q<Sprojection.length;q++){
				
					Sprojection[q] = new FldSpec(new RelSpec(RelSpec.outer), q+1);
				}  
				
				FileScan am = null;
				
			    try {
			      am  = new FileScan(updatedFileName+".in", attrTypeList[tableIndex], stringSizesList[tableIndex], 
							  (short)numOfColsList[tableIndex], (short)numOfColsList[tableIndex],
							  Sprojection, null);
			      
			      /*Tuple t1;
					while((t1 =am.get_next())!=null){
						t1.print(attrTypeList[tableIndex]);
					}*/		
			      sm.DeleteTopNRAJoin(am,tableIndex);
					
			    }
			    catch (Exception e) {
			     System.err.println (""+e);
			    }

			    
			}catch(Exception e){
				e.printStackTrace();
			}
			
		}
		
	}

	
	public static void main(String[] args) {
		
		jjoin = new PhaseIIITestSC();
		
		//JoinsDriver2 jjoin = new JoinsDriver2();

		System.out.println("DBI Phase III NRA WITH STREAM COMBINE ");
		jjoin.scanner = new Scanner(System.in);
		
		int flag = 1;
		try{
		
			/*Scanner scanner = new Scanner(System.in);
			BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));*/
            //String input = reader.readLine();
            
			while(flag==1){
				System.out.println("Enter the operation to be performed\n 1 -> TopNRAJoin \n 2 -> Add new records \n 3 -> Delete records\n 0 -> Exit ");				
				int option = jjoin.scanner.nextInt();
				
				switch(option){
				
					case 1: 
							jjoin.processTopNRAJoin();
							
						break;
					case 2: jjoin.addRecords();
						break;
					case 3: jjoin.deleteRecords();
						break;
					case 0:
						System.out.println("Goodbye");
						break;
				}
				
				try {
					//scanner.nextLine();
					
					
					System.out.println("Do you want to continue(1/0)?");
					//scanner.nextLine();
					//if(jjoin.scanner.hasNextInt())              // if there is an int to read, read it
					     flag = jjoin.scanner.nextInt();
					//else
					  //   System.out.println("Input is not an integer");
					//flag = jjoin.scanner.nextInt();
					
					System.out.println("flag="+flag);
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}catch(Exception e){
			
		}/*finally{
			scanner.close();
		}*/


	}

}
