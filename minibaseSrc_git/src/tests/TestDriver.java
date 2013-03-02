package tests;
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
import heap.InvalidSlotNumberException;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.SpaceNotAvailableException;
import heap.Tuple;
import iterator.CondExpr;
import iterator.FileScan;
import iterator.FileScanException;
import iterator.InvalidRelation;
import iterator.Iterator;
import iterator.FldSpec;
import iterator.RelSpec;
import iterator.Sort;
import iterator.SortException;
import iterator.TopRankJoin;
import iterator.TopRankJoinException;
import iterator.TupleUtilsException;

import java.io.*;
import java.util.Vector;


import chainexception.*;

//    Major Changes:
//    1. Change the return type of test() functions from 'int' to 'boolean'
//       to avoid defining static int TRUE/FALSE, which makes it easier for
//       derived functions to return the right type.
//    2. Function runTest is not implemented to avoid dealing with function
//       pointers.  Instead, it's flattened in runAllTests() function.
//    3. Change
//          Status TestDriver::runTests()
//     	    Status TestDriver::runAllTests()
//       to
//          public boolean runTests();
//          protected boolean runAllTests();

/** 
 * TestDriver class is a base class for various test driver
 * objects.
 * <br>
 * Note that the code written so far is very machine dependent.  It assumes
 * the users are on UNIX system.  For example, in function runTests, a UNIX
 * command is called to clean up the working directories.
 * 
 */
class R1 {
	  public int    sid;
	  public String sname;
	  public float score;
	  
	  public R1 (int _sid, String _sname, float _score) {
	    sid    = _sid;
	    sname  = _sname;
	    score = _score;
	  }
	}

class R2 {
	  public int    sid;
	  public String sname;
	  public int age;
	  public float score;
	  
	  public R2 (int _sid, String _sname, int _age,float _score) {
	    sid    = _sid;
	    sname  = _sname;
	    age = _age;
	    score = _score;
	  }
	}
public class TestDriver {

  public final static boolean OK   = true; 
  public final static boolean FAIL = false; 

  protected String dbpath;  
  protected String logpath;
  
  private Vector R1;
  private Vector R2;
  
  Iterator[] iteratorList = new Iterator[2];
  /** 
   * TestDriver Constructor 
   *
   * @param nameRoot The name of the test being run
   */

  protected TestDriver (String nameRoot) {
	  
	  R1  = new Vector();
	  R2  = new Vector();
	  
	  R1.addElement(new R1(1, "Bob Holloway", 0.2f));
	  R1.addElement(new R1(2, "abc", 0.4f));
	  R1.addElement(new R1(3, "def", 0.5f));
	  
	  R2.addElement(new R2(1, "Bob Holloway", 12,  0.2f));
	  R2.addElement(new R2(2, "abc", 16, 0.4f));
	  R2.addElement(new R2(3, "def", 19, 0.5f));
	  
	  int numberR1 = 3;
	  int numberR2 = 3;
	  Tuple t = new Tuple();
	  Tuple t1 = new Tuple();
	  short[] strSizes = new short[1];
	  strSizes[0] = 25;
	  AttrType[][] attrTypeList = new AttrType[2][];
	    attrTypeList[0][0] = new AttrType(AttrType.attrInteger);
	    attrTypeList[0][1] = new AttrType(AttrType.attrString);
	    attrTypeList[0][2] = new AttrType(AttrType.attrReal);
	    
	    attrTypeList[1][0] = new AttrType(AttrType.attrInteger);
	    attrTypeList[1][1] = new AttrType(AttrType.attrString);
	    attrTypeList[1][2] = new AttrType(AttrType.attrInteger);
	    attrTypeList[1][3] = new AttrType(AttrType.attrReal);
	  try {
		t.setHdr((short)3, attrTypeList[0], strSizes);
		t1.setHdr((short)3, attrTypeList[1], strSizes);
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
	  RID             rid;
	    Heapfile        f = null;
	    Heapfile        f1 = null;
	    try {
	      f = new Heapfile("R1.in");
	      f1 = new Heapfile("R2.in");
	    }
	    catch (Exception e) {
	      System.err.println("*** error in Heapfile constructor ***");
	      //status = FAIL;
	      e.printStackTrace();
	    }
	  for(int i=0;i<numberR1;i++){
		  try {
			t.setFloFld(1, ((R1)R1.elementAt(i)).sid);
			t.setStrFld(1, ((R1)R1.elementAt(i)).sname);
			t.setFloFld(1, ((R1)R1.elementAt(i)).score);
			try {
				rid=f.insertRecord(t.getTupleByteArray());
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
			}
		} catch (FieldNumberOutOfBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	  }
	  
	  for(int i=0;i<numberR2;i++){
		  try {
			t1.setIntFld(1, ((R2)R2.elementAt(i)).sid);
			t1.setStrFld(1, ((R2)R2.elementAt(i)).sname);
			t1.setIntFld(1, ((R2)R2.elementAt(i)).age);
			t1.setFloFld(1, ((R2)R2.elementAt(i)).score);
			try {
				rid=f1.insertRecord(t.getTupleByteArray());
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
			}
		} catch (FieldNumberOutOfBoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	  }
	  FldSpec[] tProjection = {new FldSpec(new RelSpec(RelSpec.outer), 1),
			  new FldSpec(new RelSpec(RelSpec.outer), 2),
			  new FldSpec(new RelSpec(RelSpec.outer), 3)};
	  
	  FldSpec[] tProjection1 = {new FldSpec(new RelSpec(RelSpec.outer), 1),
			  new FldSpec(new RelSpec(RelSpec.outer), 2),
			  new FldSpec(new RelSpec(RelSpec.outer), 3),
			  new FldSpec(new RelSpec(RelSpec.outer), 4)};
	  
	  FileScan fm1 = null;
	  FileScan fm2 = null;
	
			try {
				fm1 = new FileScan("R1.in", attrTypeList[0], strSizes,
						(short)3, 3,
						tProjection, null);
			} catch (FileScanException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (TupleUtilsException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (InvalidRelation e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
	  TupleOrder descending = new TupleOrder(TupleOrder.Descending);
		Iterator topIterator = null;
		try {
			topIterator = new Sort(attrTypeList[0], (short)attrTypeList[0].length, strSizes,fm1, 3, descending, 4, 5 );
		} catch (SortException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		try {
			fm2 = new FileScan("R2.in", attrTypeList[1], strSizes,
					(short)4, 4,
					tProjection1, null);
		} catch (FileScanException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (TupleUtilsException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (InvalidRelation e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		Iterator topIterator1 = null;
		try {
			topIterator1 = new Sort(attrTypeList[1], (short)attrTypeList[1].length, strSizes,fm2, 4, descending, 4, 5 );
		} catch (SortException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		iteratorList[0] = topIterator;
		iteratorList[1] = topIterator1;
  //  sprintf( dbpath, MINIBASE_DB, nameRoot, getpid() );
  //  sprintf( logpath, MINIBASE_LOG, nameRoot, getpid() );

    //NOTE: Assign random numbers to the dbpath doesn't work because
    //we can never open the same database again if everytime we are
    //given a different number.  

    //To port it to a different platform, get "user.name" should
    //still work well because this feature is not meant to be UNIX
    //dependent. 
    dbpath = "F:\\jyothi.minibase-db"; 
    logpath = "F:\\jyothi.minibase-log"; 
  }

  /**
   * Another Constructor
   */

  protected TestDriver () {}

  /** 
   * @return whether the test has completely successfully 
   */
  protected boolean test1 () { return true; }
  
  /** 
   * @return whether the test has completely successfully 
   */
  protected boolean test2 () { return true; }

  /** 
   * @return whether the test has completely successfully 
   */
  protected boolean test3 () { return true; }

  /** 
   * @return whether the test has completely successfully 
   */
  protected boolean test4 () { return true; }

  /** 
   * @return whether the test has completely successfully 
   */
  protected boolean test5 () { return true; }

  /** 
   * @return whether the test has completely successfully 
   */
  protected boolean test6 () { return true; }

  /** 
   * @return <code>String</code> object which contains the name of the test
   */
  protected String testName() { 

    //A little reminder to subclassers 
    return "*** unknown ***"; 

  }

  /**
   * This function does the preparation/cleaning work for the
   * running tests.
   *
   * @return a boolean value indicates whether ALL the tests have passed
   */
  public boolean runTests ()  {
    
    System.out.println ("\n" + "Running " + testName() + " tests...." + "\n");
    
    // Kill anything that might be hanging around
    String newdbpath;
    String newlogpath;
    String remove_logcmd;
    String remove_dbcmd;
    String remove_cmd = "/bin/rm -rf ";

    newdbpath = dbpath;
    newlogpath = logpath;

    remove_logcmd = remove_cmd + logpath;
    remove_dbcmd = remove_cmd + dbpath;

    // Commands here is very machine dependent.  We assume
    // user are on UNIX system here
    try {
      Runtime.getRuntime().exec(remove_logcmd);
      Runtime.getRuntime().exec(remove_dbcmd);
    } 
    catch (IOException e) {
      System.err.println (""+e);
    }
    
    remove_logcmd = remove_cmd + newlogpath;
    remove_dbcmd = remove_cmd + newdbpath;

    //This step seems redundant for me.  But it's in the original
    //C++ code.  So I am keeping it as of now, just in case I
    //I missed something
    try {
      Runtime.getRuntime().exec(remove_logcmd);
      Runtime.getRuntime().exec(remove_dbcmd);
    } 
    catch (IOException e) {
      System.err.println (""+e);
    }

    //Run the tests. Return type different from C++
    boolean _pass = runAllTests();

    //Clean up again
    try {
      Runtime.getRuntime().exec(remove_logcmd);
      Runtime.getRuntime().exec(remove_dbcmd);
    } 
    catch (IOException e) {
      System.err.println (""+e);
    }
    
    System.out.println ("\n" + "..." + testName() + " tests ");
    System.out.print (_pass==OK ? "completely successfully" : "failed");
    System.out.println (".\n\n");
    
    return _pass;
  }
public static void main(String args[]){
	TestDriver test = new TestDriver();
	test.runAllTests();
}
  protected boolean runAllTests() {

    boolean _passAll = OK;

    //The following code checks whether appropriate erros have been logged,
    //which, if implemented, should be done for each test case.  

    //minibase_errors.clear_errors();
    //int result = test();
    //if ( !result || minibase_errors.error() ) {
    //  status = FAIL;
    //  if ( minibase_errors.error() )
    //    cerr << (result? "*** Unexpected error(s) logged, test failed:\n"
    //    : "Errors logged:\n");
    //    minibase_errors.show_errors(cerr);
    //}
    
    //The following runs all the test functions without checking
    //the logged error types. 

    //Running test1() to test6()
    if (!test1()) { _passAll = FAIL; }
    int numOfTables = 2;
    AttrType[][] attrTypeList = new AttrType[2][];
    attrTypeList[0] = new AttrType[3];
    attrTypeList[0][0] = new AttrType(AttrType.attrInteger);
    attrTypeList[0][1] = new AttrType(AttrType.attrString);
    attrTypeList[0][2] = new AttrType(AttrType.attrReal);
    
    attrTypeList[1] = new AttrType[4];
    attrTypeList[1][0] = new AttrType(AttrType.attrInteger);
    attrTypeList[1][1] = new AttrType(AttrType.attrString);
    attrTypeList[1][2] = new AttrType(AttrType.attrInteger);
    attrTypeList[1][3] = new AttrType(AttrType.attrReal);
    
    int[] numOfColsList = new int[2];
    numOfColsList[0] = attrTypeList[0].length;
    numOfColsList[1] = attrTypeList[1].length;
    
    short[][] stringSizesList = new short[2][];
    stringSizesList[0] = new short[1];
    stringSizesList[1] = new short[1];

    stringSizesList[0][0] = 25;
    stringSizesList[1][0] = 25;
    
    int[] joinedColList = new int[2];
    joinedColList[0]=0;
    joinedColList[1]=0;
    
   
    IndexType[] b_index = new IndexType[2];
    b_index[0] = new IndexType(IndexType.B_Index);
    b_index[1] = new IndexType(IndexType.B_Index);
    
    String[] indexNameList = new String[2];
    int memory = 10;
    CondExpr[] condExprList = new CondExpr[1];
    condExprList[0] = new CondExpr();
    condExprList[0].op   = new AttrOperator(AttrOperator.aopGT);
    condExprList[0].next = null;
    condExprList[0].type1 = new AttrType(AttrType.attrSymbol);
    condExprList[0].type2 = new AttrType(AttrType.attrString);
    condExprList[0].operand1.symbol = new FldSpec (new RelSpec(RelSpec.innerRel),3);
    condExprList[0].operand2.integer=5;
    
    FldSpec[] projList = {
    	       new FldSpec(new RelSpec(RelSpec.outer), 2),
    	       new FldSpec(new RelSpec(RelSpec.innerRel), 2),
    	       new FldSpec(new RelSpec(RelSpec.innerRel), 3)
    	    };
    int projlistIndex = 3;
    int topK= 2;
    
    try {
		TopRankJoin trj = new TopRankJoin(numOfTables, attrTypeList, numOfColsList, stringSizesList, 
joinedColList, iteratorList, b_index, indexNameList, memory, condExprList, projList, projlistIndex, topK, 1 );
	} catch (TopRankJoinException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	} catch (IOException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	}
	
    //if (!test2()) { _passAll = FAIL; }
    //if (!test3()) { _passAll = FAIL; }
    //if (!test4()) { _passAll = FAIL; }
    //if (!test5()) { _passAll = FAIL; }
    //if (!test6()) { _passAll = FAIL; }

    return _passAll;
  }

  /**
   * Used to verify whether the exception thrown from
   * the bottom layer is the one expected.
   */
  public boolean checkException (ChainException e, 
				 String expectedException) {

    boolean notCaught = true;
    while (true) {
      
      String exception = e.getClass().getName();
      
      if (exception.equals(expectedException)) {
	return (!notCaught);
      }
      
      if ( e.prev==null ) {
	return notCaught;
      }
      e = (ChainException)e.prev;
    }
    
  } // end of checkException
  
} // end of TestDriver  
