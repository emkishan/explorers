package tests;
import global.AttrOperator;
import global.AttrType;
import global.GlobalConst;
import global.IndexType;
import global.RID;
import global.SystemDefs;
import global.TupleOrder;
import heap.FieldNumberOutOfBoundException;
import heap.HFBufMgrException;
import heap.HFDiskMgrException;
import heap.HFException;
import heap.Heapfile;
import heap.InvalidSlotNumberException;
import heap.InvalidTupleSizeException;
import heap.InvalidTypeException;
import heap.Scan;
import heap.SpaceNotAvailableException;
import heap.Tuple;
import index.IndexException;
import iterator.CondExpr;
import iterator.FileScan;
import iterator.FileScanException;
import iterator.InvalidRelation;
import iterator.Iterator;
import iterator.FldSpec;
import iterator.JoinsException;
import iterator.LowMemException;
import iterator.PredEvalException;
import iterator.RelSpec;
import iterator.Sort;
import iterator.SortException;
import iterator.TopRankJoin;
import iterator.TopRankJoinException;
import iterator.TupleUtilsException;
import iterator.UnknowAttrType;
import iterator.UnknownKeyTypeException;

import java.io.*;
import java.util.Vector;

import btree.BTreeFile;
import btree.IntegerKey;
import bufmgr.PageNotReadException;


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

class R3 {
	  public int    sid;
	  public String sname;
	  public int age;
	  public float score;
	  
	  public R3 (int _sid, String _sname, int _age,float _score) {
	    sid    = _sid;
	    sname  = _sname;
	    age = _age;
	    score = _score;
	  }
	}

class R4 {
	  public int    sid;
	  public String sname;
	  public int age;
	  public float score;
	  
	  public R4 (int _sid, String _sname, int _age,float _score) {
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
  private Vector R3;
  private Vector R4;
  SystemDefs sysdef;
  
  Iterator[] iteratorList = new Iterator[4];
  /** 
   * TestDriver Constructor 
   *
   * @param nameRoot The name of the test being run
   */

  protected TestDriver (String nameRoot) {
	    dbpath = "\\tmp\\kishan.minibase.db"; 
	    logpath = "\\tmp\\kishan.minibase.log"; 
	  R1  = new Vector();
	  R2  = new Vector();
	  R3 = new Vector();
	  R4 = new Vector();
	  
	  R1.addElement(new R1(1, "Bob Holloway", (float) 0.2));
	  R1.addElement(new R1(2, "abc", (float) 0.4));
	  R1.addElement(new R1(3, "def", (float) 0.5));
	  R1.addElement(new R1(4, "ghi", (float) 0.45));
/*	  R1.addElement(new R1(5, "Bob Holloway", (float) 0.2));
	  R1.addElement(new R1(6, "abc", (float) 0.4));
	  R1.addElement(new R1(7, "def", (float) 0.5));
	  R1.addElement(new R1(8, "ghi", (float) 0.45));*/

	  
	  R2.addElement(new R2(1, "Bob Holloway", 13,  (float) 0.2));
	  R2.addElement(new R2(2, "abc", 16, (float) 0.4));
	  R2.addElement(new R2(3, "def", 19, (float) 0.5));
	  R2.addElement(new R2(3, "def", 20, (float) 0.55));
	  R2.addElement(new R2(4, "bmw", 9, (float) 0.47));
/*	  R2.addElement(new R2(5, "Bob Holloway", 13,  (float) 0.2));
	  R2.addElement(new R2(6, "abc", 16, (float) 0.4));
	  R2.addElement(new R2(7, "def", 19, (float) 0.5));
	  R2.addElement(new R2(8, "def", 20, (float) 0.55));
	  R2.addElement(new R2(8, "bmw", 9, (float) 0.47));*/
	  
	  R3.addElement(new R3(1, "Bob Holloway", 13,  (float) 0.2));
	  R3.addElement(new R3(2, "abc", 16, (float) 0.4));
	  R3.addElement(new R3(3, "def", 19, (float) 0.6));
	 // R2.addElement(new R2(3, "def", 20, (float) 0.55));
	  R3.addElement(new R3(4, "bmw", 9, (float) 0.57));
/*	  R3.addElement(new R3(5, "Bob Holloway", 13,  (float) 0.2));
	  R3.addElement(new R3(6, "abc", 16, (float) 0.4));
	  R3.addElement(new R3(7, "def", 19, (float) 0.6));
	 // R2.addElement(new R2(3, "def", 20, (float) 0.55));
	  R3.addElement(new R3(8, "bmw", 9, (float) 0.57));*/
	  
	  
	  R4.addElement(new R4(1, "Bob Holloway", 13,  (float) 0.2));
	  R4.addElement(new R4(2, "abc", 16, (float) 0.4));
	  R4.addElement(new R4(3, "def", 19, (float) 0.6));
	 //R2.addElement(new R2(3, "def", 20, (float) 0.55));
	  R4.addElement(new R4(4, "bmw", 9, (float) 0.57));
	  
	  int numberR1 = 4;
	  int numberR2 = 4;
	  int numberR3 = 4;
	  int numberR4 = 4;
	  Tuple t = new Tuple();
	  Tuple t1 = new Tuple();
	  Tuple tt = new Tuple();
	  Tuple t2 = new Tuple();
	  Tuple t3 = new Tuple();
	  Tuple t4 = new Tuple();
	  Tuple t5 = new Tuple();
	  short[] strSizes = new short[1];
	  strSizes[0] = 25;
	  AttrType[][] attrTypeList = new AttrType[4][];
	  	attrTypeList[0] = new AttrType[3];
	    attrTypeList[0][0] = new AttrType(AttrType.attrInteger);
	    attrTypeList[0][1] = new AttrType(AttrType.attrString);
	    attrTypeList[0][2] = new AttrType(AttrType.attrReal);
	    
	    attrTypeList[1] = new AttrType[4];
	    attrTypeList[1][0] = new AttrType(AttrType.attrInteger);
	    attrTypeList[1][1] = new AttrType(AttrType.attrString);
	    attrTypeList[1][2] = new AttrType(AttrType.attrInteger);
	    attrTypeList[1][3] = new AttrType(AttrType.attrReal);
	    
	    attrTypeList[2] = new AttrType[4];
	    attrTypeList[2][0] = new AttrType(AttrType.attrInteger);
	    attrTypeList[2][1] = new AttrType(AttrType.attrString);
	    attrTypeList[2][2] = new AttrType(AttrType.attrInteger);
	    attrTypeList[2][3] = new AttrType(AttrType.attrReal);
	    
	    attrTypeList[3] = new AttrType[4];
	    attrTypeList[3][0] = new AttrType(AttrType.attrInteger);
	    attrTypeList[3][1] = new AttrType(AttrType.attrString);
	    attrTypeList[3][2] = new AttrType(AttrType.attrInteger);
	    attrTypeList[3][3] = new AttrType(AttrType.attrReal);
	  try {
		t.setHdr((short)3, attrTypeList[0], strSizes);
		tt.setHdr((short)3, attrTypeList[0], strSizes);
		t1.setHdr((short)4, attrTypeList[1], strSizes);
		t2.setHdr((short)4, attrTypeList[1], strSizes);
		t3.setHdr((short)4, attrTypeList[2], strSizes);
		t4.setHdr((short)4, attrTypeList[2], strSizes);
		t5.setHdr((short)4, attrTypeList[3], strSizes);
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
	  sysdef = new SystemDefs( dbpath, 1000, GlobalConst.NUMBUF, "Clock" );
	  RID             rid;
	    Heapfile        f = null;
	    Heapfile        f1 = null;
	    Heapfile f2 = null;
	    Heapfile f3 = null;
	    try {
	      f = new Heapfile("R1.in");
	      f1 = new Heapfile("R2.in");
	      f2 = new Heapfile("R3.in");
	      f3 = new Heapfile("R4.in");
	    }
	    catch (Exception e) {
	      System.err.println("*** error in Heapfile constructor ***");
	      //status = FAIL;
	      e.printStackTrace();
	    }
	  for(int i=0;i<numberR1;i++){
		  try {
			t.setIntFld(1, ((R1)R1.elementAt(i)).sid);
			t.setStrFld(2, ((R1)R1.elementAt(i)).sname);
			t.setFloFld(3, ((R1)R1.elementAt(i)).score);
			t.setScore(((R1)R1.elementAt(i)).score);
			
			
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
			t1.setStrFld(2, ((R2)R2.elementAt(i)).sname);
			t1.setIntFld(3, ((R2)R2.elementAt(i)).age);
			t1.setFloFld(4, ((R2)R2.elementAt(i)).score);
			t1.setScore(((R2)R2.elementAt(i)).score);
			
			try {
				rid=f1.insertRecord(t1.getTupleByteArray());
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
	  
	  for(int i=0;i<numberR3;i++){
		  try {
			t3.setIntFld(1, ((R3)R3.elementAt(i)).sid);
			t3.setStrFld(2, ((R3)R3.elementAt(i)).sname);
			t3.setIntFld(3, ((R3)R3.elementAt(i)).age);
			t3.setFloFld(4, ((R3)R3.elementAt(i)).score);
			t3.setScore(((R3)R3.elementAt(i)).score);
			
			try {
				rid=f2.insertRecord(t3.getTupleByteArray());
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
	  
	  for(int i=0;i<numberR4;i++){
		  try {
			t5.setIntFld(1, ((R4)R4.elementAt(i)).sid);
			t5.setStrFld(2, ((R4)R4.elementAt(i)).sname);
			t5.setIntFld(3, ((R4)R4.elementAt(i)).age);
			t5.setFloFld(4, ((R4)R4.elementAt(i)).score);
			t5.setScore(((R4)R4.elementAt(i)).score);
			
			try {
				rid=f3.insertRecord(t5.getTupleByteArray());
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
	  
	  
	  FldSpec[] tProjection2 = {new FldSpec(new RelSpec(RelSpec.outer), 1),
			  new FldSpec(new RelSpec(RelSpec.outer), 2),
			  new FldSpec(new RelSpec(RelSpec.outer), 3),
			  new FldSpec(new RelSpec(RelSpec.outer), 4)};
	  
	  FldSpec[] tProjection3 = {new FldSpec(new RelSpec(RelSpec.outer), 1),
			  new FldSpec(new RelSpec(RelSpec.outer), 2),
			  new FldSpec(new RelSpec(RelSpec.outer), 3),
			  new FldSpec(new RelSpec(RelSpec.outer), 4)};
	  
	  FileScan fm1 = null;
	  FileScan fm2 = null;
	  FileScan fm3 = null;
	  FileScan fm4 = null;
	
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
		
		
		try {
			fm3 = new FileScan("R3.in", attrTypeList[1], strSizes,
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
		
		Iterator topIterator2 = null;
		try {
			topIterator2 = new Sort(attrTypeList[2], (short)attrTypeList[2].length, strSizes,fm3, 4, descending, 4, 5 );
		} catch (SortException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		
		try {
			fm4 = new FileScan("R4.in", attrTypeList[1], strSizes,
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
		
		Iterator topIterator3 = null;
		try {
			topIterator3 = new Sort(attrTypeList[2], (short)attrTypeList[2].length, strSizes,fm4, 4, descending, 4, 5 );
		} catch (SortException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		boolean newTupleFlag=true;
		 BTreeFile btf1 = null;
		    try {
		      btf1 = new BTreeFile("BTreeIndex2", AttrType.attrInteger, 4, 1); 
		    }
		    catch (Exception e) {
		      //status = FAIL;
		      e.printStackTrace();
		      Runtime.getRuntime().exit(1);
		    }
		    Scan scan = null;
		    
		    try {
		      scan = new Scan(f);
	}
   catch (Exception e) {
     //status = FAIL;
     e.printStackTrace();
     Runtime.getRuntime().exit(1);
   }
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
		    	  tupleKey = tt.getIntFld(1);
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
		    
		    
		    // Btree for second file
		    
		    BTreeFile btf2 = null;
		    try {
		      btf2 = new BTreeFile("BTreeIndex3", AttrType.attrInteger, 4, 1); 
		    }
		    catch (Exception e) {
		      //status = FAIL;
		      e.printStackTrace();
		      Runtime.getRuntime().exit(1);
		    }
		    Scan scan1 = null;
		    
		    try {
		      scan1 = new Scan(f1);
	}
   catch (Exception e) {
     //status = FAIL;
     e.printStackTrace();
     Runtime.getRuntime().exit(1);
   }	
		    RID scanRid1 = new RID();
		    int tupleKey1 =0;
		    Tuple temp1 = null;
		    
		    try {
		      temp1 = scan1.getNext(scanRid1);
		    }
		    catch (Exception e) {
		      e.printStackTrace();
		    }
		    while ( temp1 != null) {
		      t2.tupleCopy(temp1);
		      
		      try {
		    	  tupleKey1 = t2.getIntFld(1);
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }
		      
		      try {
			btf2.insert(new IntegerKey(tupleKey1), scanRid1); 
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }

		      try {
			temp1 = scan1.getNext(scanRid1);
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }
		    }
		    scan1.closescan();
		    
		    
		    BTreeFile btf3 = null;
		    try {
		      btf3 = new BTreeFile("BTreeIndex4", AttrType.attrInteger, 4, 1); 
		    }
		    catch (Exception e) {
		      //status = FAIL;
		      e.printStackTrace();
		      Runtime.getRuntime().exit(1);
		    }
		    Scan scan2 = null;
		    
		    try {
		      scan2 = new Scan(f2);
	}
   catch (Exception e) {
     //status = FAIL;
     e.printStackTrace();
     Runtime.getRuntime().exit(1);
   }
		    RID scanRid2 = new RID();
		    int tupleKey2 =0;
		    Tuple temp2 = null;
		    
		    try {
		      temp2 = scan2.getNext(scanRid2);
		    }
		    catch (Exception e) {
		      e.printStackTrace();
		    }
		    while ( temp2 != null) {
		      t4.tupleCopy(temp2);
		      
		      try {
		    	  tupleKey2 = t4.getIntFld(1);
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }
		      
		      try {
			btf3.insert(new IntegerKey(tupleKey2), scanRid2); 
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }

		      try {
			temp2 = scan2.getNext(scanRid2);
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }
		    }
		    scan2.closescan();
		    
		    BTreeFile btf4 = null;
		    try {
		      btf4 = new BTreeFile("BTreeIndex5", AttrType.attrInteger, 4, 1); 
		    }
		    catch (Exception e) {
		      //status = FAIL;
		      e.printStackTrace();
		      Runtime.getRuntime().exit(1);
		    }
		    Scan scan3 = null;
		    
		    try {
		      scan3 = new Scan(f3);
	}
   catch (Exception e) {
     //status = FAIL;
     e.printStackTrace();
     Runtime.getRuntime().exit(1);
   }
		    RID scanRid3 = new RID();
		    int tupleKey3 =0;
		    Tuple temp3 = null;
		    
		    try {
		      temp3 = scan3.getNext(scanRid3);
		    }
		    catch (Exception e) {
		      e.printStackTrace();
		    }
		    while ( temp3 != null) {
		      t5.tupleCopy(temp3);
		      
		      try {
		    	  tupleKey3 = t5.getIntFld(1);
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }
		      
		      try {
			btf4.insert(new IntegerKey(tupleKey3), scanRid3); 
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }

		      try {
			temp3 = scan3.getNext(scanRid3);
		      }
		      catch (Exception e) {
			e.printStackTrace();
		      }
		    }
		    scan3.closescan();
		    
		iteratorList[0] = topIterator;
		iteratorList[1] = topIterator1;
		iteratorList[2] = topIterator2;
		iteratorList[3] = topIterator3;
		Tuple tuple1 = new Tuple();
		try {
			tuple1.setHdr((short)3, attrTypeList[0], strSizes);
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
			/*try {
				while ((tuple1 = topIterator.get_next()) != null) {
					tuple1.print(tuple1.attr_Types);
				}
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
			}*/
  //  sprintf( dbpath, MINIBASE_DB, nameRoot, getpid() );
  //  sprintf( logpath, MINIBASE_LOG, nameRoot, getpid() );

    //NOTE: Assign random numbers to the dbpath doesn't work because
    //we can never open the same database again if everytime we are
    //given a different number.  

    //To port it to a different platform, get "user.name" should
    //still work well because this feature is not meant to be UNIX
    //dependent. 

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
	TestDriver test = new TestDriver("Deepu");
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
    int numOfTables = 4;
    AttrType[][] attrTypeList = new AttrType[4][];
    attrTypeList[0] = new AttrType[3];
    attrTypeList[0][0] = new AttrType(AttrType.attrInteger);
    attrTypeList[0][1] = new AttrType(AttrType.attrString);
    attrTypeList[0][2] = new AttrType(AttrType.attrReal);
    
    attrTypeList[1] = new AttrType[4];
    attrTypeList[1][0] = new AttrType(AttrType.attrInteger);
    attrTypeList[1][1] = new AttrType(AttrType.attrString);
    attrTypeList[1][2] = new AttrType(AttrType.attrInteger);
    attrTypeList[1][3] = new AttrType(AttrType.attrReal);
    
    attrTypeList[2] = new AttrType[4];
    attrTypeList[2][0] = new AttrType(AttrType.attrInteger);
    attrTypeList[2][1] = new AttrType(AttrType.attrString);
    attrTypeList[2][2] = new AttrType(AttrType.attrInteger);
    attrTypeList[2][3] = new AttrType(AttrType.attrReal);
    
    attrTypeList[3] = new AttrType[4];
    attrTypeList[3][0] = new AttrType(AttrType.attrInteger);
    attrTypeList[3][1] = new AttrType(AttrType.attrString);
    attrTypeList[3][2] = new AttrType(AttrType.attrInteger);
    attrTypeList[3][3] = new AttrType(AttrType.attrReal);
    
    int[] numOfColsList = new int[4];
    numOfColsList[0] = attrTypeList[0].length;
    numOfColsList[1] = attrTypeList[1].length;
    numOfColsList[2] = attrTypeList[2].length;
    numOfColsList[3] = attrTypeList[3].length;
    
    short[][] stringSizesList = new short[4][];
    stringSizesList[0] = new short[1];
    stringSizesList[1] = new short[1];
    stringSizesList[2] = new short[1];
    stringSizesList[3] = new short[1];

    stringSizesList[0][0] = 25;
    stringSizesList[1][0] = 25;
    stringSizesList[2][0] = 25;
    stringSizesList[3][0] = 25;
    
    int[] joinedColList = new int[4];
    joinedColList[0]=0;
    joinedColList[1]=0;
    joinedColList[2]=0;
    joinedColList[3]=0;
    
   
    IndexType[] b_index = new IndexType[4];
    b_index[0] = new IndexType(IndexType.B_Index);
    b_index[1] = new IndexType(IndexType.B_Index);
    b_index[2] = new IndexType(IndexType.B_Index);
    b_index[3] = new IndexType(IndexType.B_Index);
    
    String[] indexNameList = new String[4];
    indexNameList[0] = "BTreeIndex2";
    indexNameList[1] = "BTreeIndex3";
    indexNameList[2] = "BTreeIndex4";
    indexNameList[3] = "BTreeIndex5";
    
    int memory = 10;
    CondExpr[] condExprList = new CondExpr[2];
    condExprList[0] = new CondExpr();
    condExprList[0].op   = new AttrOperator(AttrOperator.aopGT);
    condExprList[0].next = null;
    condExprList[0].type1 = new AttrType(AttrType.attrSymbol);
    condExprList[0].type2 = new AttrType(AttrType.attrSymbol);
    condExprList[0].operand1.symbol = new FldSpec (new RelSpec(RelSpec.outer),1);
    condExprList[0].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel),3);
    
    condExprList[1] = new CondExpr();
    condExprList[1].op   = new AttrOperator(AttrOperator.aopGT);
    condExprList[1].next = null;
    condExprList[1].type1 = new AttrType(AttrType.attrSymbol);
    condExprList[1].type2 = new AttrType(AttrType.attrInteger);
    condExprList[1].operand1.symbol = new FldSpec (new RelSpec(RelSpec.innerRel),3);
    //condExprList[1].operand2.symbol = new FldSpec(new RelSpec(RelSpec.innerRel),3);
    condExprList[1].operand2.integer = 12;
    
    FldSpec[] projList = {
    	       new FldSpec(new RelSpec(RelSpec.outer), 2),
    	       new FldSpec(new RelSpec(RelSpec.innerRel), 2),
    	       new FldSpec(new RelSpec(RelSpec.innerRel), 3),
    	       new FldSpec(new RelSpec(RelSpec.outer), 1),
    	       new FldSpec(new RelSpec(2), 2),
    	       new FldSpec(new RelSpec(2), 3),
    	       new FldSpec(new RelSpec(3), 2),
    	       new FldSpec(new RelSpec(3), 3),
    	    };
    int projlistIndex = 8;
    int topK= 2;
    
    String[] fileNames = new String[4];
    fileNames[0] = "R1.in";
    fileNames[1] = "R2.in";
    fileNames[2] = "R3.in";
    fileNames[3] = "R4.in";
    
    try {
    	long startTime = System.currentTimeMillis();
    	System.out.println("Before " + sysdef.JavabaseBM.getPageAccessCount());
		TopRankJoin trj = new TopRankJoin(numOfTables, attrTypeList, numOfColsList, stringSizesList, 
joinedColList, iteratorList, b_index, indexNameList, memory, condExprList, projList, projlistIndex, topK, 1 , fileNames);
		System.out.println("After " + sysdef.JavabaseBM.getPageAccessCount());
		long endTime = System.currentTimeMillis();
		System.out.println("Total Time = " + (endTime-startTime));
		for(int k=0;k<4;k++)
			System.out.println("Probed " + trj.num_probed(k));
		for(int k=0;k<4;k++)
			System.out.println("Scanned " + trj.num_scanned(k));
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
