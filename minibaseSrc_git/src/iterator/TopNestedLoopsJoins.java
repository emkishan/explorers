package iterator;
   

import heap.*;
import global.*;
import bufmgr.*;
import diskmgr.*;
import index.*;

import java.lang.*;
import java.io.*;
/** 
 *
 *  This file contains an implementation of the nested loops join
 *  algorithm as described in the Shapiro paper.
 *  The algorithm is extremely simple:
 *
 *      foreach tuple r in R do
 *          foreach tuple s in S do
 *              if (ri == sj) then add (r, s) to the result.
 */

public class TopNestedLoopsJoins  extends Iterator 
{
  private AttrType      _in1[],  _in2[];
  private   int        in1_len, in2_len;
  private   Iterator  outer;
  private   short t2_str_sizescopy[];
  private   CondExpr OutputFilter[];
  private   CondExpr RightFilter[];
  private   int        n_buf_pgs;        // # of buffer pages available.
  private   boolean        done,         // Is the join complete
    get_from_outer;                 // if TRUE, a tuple is got from outer
  private   Tuple     outer_tuple, inner_tuple;
  private   Tuple     Jtuple;           // Joined tuple
  private   FldSpec   perm_mat[];
  private   int        nOutFlds;
  private   Heapfile  hf, topFile;
  private   Scan      inner;
  //added by akaranam
  private Tuple JtopTuple;
  private RID rid;
  private int topK;
  
  /**constructor
   *Initialize the two relations which are joined, including relation type,
   *@param in1  Array containing field types of R.
   *@param len_in1  # of columns in R.
   *@param t1_str_sizes shows the length of the string fields.
   *@param in2  Array containing field types of S
   *@param len_in2  # of columns in S
   *@param  t2_str_sizes shows the length of the string fields.
   *@param amt_of_mem  IN PAGES
   *@param am1  access method for left i/p to join
   *@param relationName  access hfapfile for right i/p to join
   *@param outFilter   select expressions
   *@param rightFilter reference to filter applied on right i/p
   *@param proj_list shows what input fields go where in the output tuple
   *@param n_out_flds number of outer relation fileds
   *@param num number of top elements to be queried
   *@exception IOException some I/O fault
   *@exception NestedLoopException exception from this class
   */
  public TopNestedLoopsJoins( AttrType    in1[],    
			   int     len_in1,           
			   short   t1_str_sizes[],
			   AttrType    in2[],         
			   int     len_in2,           
			   short   t2_str_sizes[],   
			   int     amt_of_mem,        
			   Iterator     am1,          
			   String relationName,      
			   CondExpr outFilter[],      
			   CondExpr rightFilter[],    
			   FldSpec   proj_list[],
			   int        n_out_flds,
			   int num
			   ) throws IOException,NestedLoopException
    {
      
      _in1 = new AttrType[in1.length];
      _in2 = new AttrType[in2.length];
      System.arraycopy(in1,0,_in1,0,in1.length);
      System.arraycopy(in2,0,_in2,0,in2.length);
      in1_len = len_in1;
      in2_len = len_in2;
      //added by akaranam
      topFile = null;

		try {
			topFile = new Heapfile("TopNestedLoop.in");
		} catch (Exception e) {
			System.out.println("Error");
		}
		
	  topK = num;
	  
	  for(int i=0;i<in1.length;i++)
    	  System.out.print(_in1[i]+"\t");
      
      outer = am1;
      
      System.out.println(outer.toString());
      
      t2_str_sizescopy =  t2_str_sizes;
      inner_tuple = new Tuple();
      Jtuple = new Tuple();
      OutputFilter = outFilter;
      RightFilter  = rightFilter;
      
      n_buf_pgs    = amt_of_mem;
      inner = null;
      done  = false;
      get_from_outer = true;
      
      AttrType[] Jtypes = new AttrType[n_out_flds];
      short[]    t_size;
      
      perm_mat = proj_list;
      nOutFlds = n_out_flds;
      try {
	t_size = TupleUtils.setup_op_tuple(Jtuple, Jtypes,
					   in1, len_in1, in2, len_in2,
					   t1_str_sizes, t2_str_sizes,
					   proj_list, nOutFlds);
      }catch (TupleUtilsException e){
	throw new NestedLoopException(e,"TupleUtilsException is caught by NestedLoopsJoins.java");
      }
      JtopTuple = new Tuple();
		AttrType[] attrType = new AttrType[Jtuple.attrSizes + 1];
		for (int i = 0; i < Jtuple.attrSizes; i++) {
			attrType[i] = Jtuple.attr_Types[i];
		}
		attrType[Jtuple.attrSizes] = new AttrType(AttrType.attrReal);
		try {
			JtopTuple.setHdr((short) (Jtuple.noOfFlds() + 1), attrType,Jtuple.string_sizes);
		} catch (InvalidTypeException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (InvalidTupleSizeException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
      
      
      
      try {
	  hf = new Heapfile(relationName);
	  
      }
      catch(Exception e) {
	throw new NestedLoopException(e, "Create new heapfile failed.");
      }
    }
  
  /**  
   *@return The joined tuple is returned
   *@exception IOException I/O errors
   *@exception JoinsException some join exception
   *@exception IndexException exception from super class
   *@exception InvalidTupleSizeException invalid tuple size
   *@exception InvalidTypeException tuple type not valid
   *@exception PageNotReadException exception from lower layer
   *@exception TupleUtilsException exception from using tuple utilities
   *@exception PredEvalException exception from PredEval class
   *@exception SortException sort exception
   *@exception LowMemException memory error
   *@exception UnknowAttrType attribute type unknown
   *@exception UnknownKeyTypeException key type unknown
   *@exception Exception other exceptions

   */
  public Tuple get_next()
    throws IOException,
	   JoinsException ,
	   IndexException,
	   InvalidTupleSizeException,
	   InvalidTypeException, 
	   PageNotReadException,
	   TupleUtilsException, 
	   PredEvalException,
	   SortException,
	   LowMemException,
	   UnknowAttrType,
	   UnknownKeyTypeException,
	   Exception
    {
      // This is a DUMBEST form of a join, not making use of any key information...
      
      
      if (done)
	return null;
      
      do
	{
	  // If get_from_outer is true, Get a tuple from the outer, delete
	  // an existing scan on the file, and reopen a new scan on the file.
	  // If a get_next on the outer returns DONE?, then the nested loops
	  //join is done too.
	  
	  if (get_from_outer == true)
	    {
	      get_from_outer = false;
	      if (inner != null)     // If this not the first time,
		{
		  // close scan
		  inner = null;
		}
	    
	      try {
		inner = hf.openScan();
	      }
	      catch(Exception e){
		throw new NestedLoopException(e, "openScan failed");
	      }
	      
	      if ((outer_tuple=outer.get_next()) == null)
		{
		  done = true;
		  if (inner != null) 
		    {
                      
		      inner = null;
		    }
		  
		  return null;
		}   
	    }  // ENDS: if (get_from_outer == TRUE)
	 
	  
	  // The next step is to get a tuple from the inner,
	  // while the inner is not completely scanned && there
	  // is no match (with pred),get a tuple from the inner.
	  
	 
	      RID rid = new RID();
	      while ((inner_tuple = inner.getNext(rid)) != null)
		{
		  inner_tuple.setHdr((short)in2_len, _in2,t2_str_sizescopy);
		  if (PredEval.Eval(RightFilter, inner_tuple, null, _in2, null) == true)
		    {
		      if (PredEval.Eval(OutputFilter, outer_tuple, inner_tuple, _in1, _in2) == true)
			{
			  // Apply a projection on the outer and inner tuples.
		      System.out.println("Outer Tuple Score before Join : " + outer_tuple.getScore());
			  //Projection.Join(outer_tuple, _in1,inner_tuple, _in2,Jtuple, perm_mat, nOutFlds);
			  Projection.TopJoin(outer_tuple, _in1,0,inner_tuple, _in2,0,Jtuple, perm_mat, nOutFlds);
			  writeTuple();
			  rid = topFile.insertRecord(JtopTuple.getTupleByteArray());
			  /*for(int i=1;i<nOutFlds;i++){
				  System.out.print("\t" + Jtuple.getStrFld(i));
			  }*/
			  System.out.print("\t" + Jtuple.getScore());
			  System.out.println();
			  return Jtuple;
			  
			}
		    }
		}
	      
	      // There has been no match. (otherwise, we would have 
	      //returned from t//he while loop. Hence, inner is 
	      //exhausted, => set get_from_outer = TRUE, go to top of loop
	      get_from_outer = true; // Loop back to top and get next outer tuple.	      
	} while (true);
    } 
 
  /**
   * implement the abstract method close() from super class Iterator
   *to finish cleaning up
   *@exception IOException I/O error from lower layers
   *@exception JoinsException join error from lower layers
   *@exception IndexException index access error 
   */
  public void close() throws JoinsException, IOException,IndexException 
    {
      if (!closeFlag) {
	
	try {
	  outer.close();
	}catch (Exception e) {
	  throw new JoinsException(e, "NestedLoopsJoin.java: error in closing iterator.");
	}
	closeFlag = true;
      }
    }
  
  public void writeTuple() throws UnknowAttrType, WrongPermat,FieldNumberOutOfBoundException, IOException {
int nOutFlds = Jtuple.attr_Types.length;
for (int i = 0; i < nOutFlds; i++) {
	switch (Jtuple.attr_Types[i].attrType) {
	case AttrType.attrInteger:
		JtopTuple.setIntFld(i + 1, Jtuple.getIntFld(i + 1));
		break;
	case AttrType.attrReal:
		JtopTuple.setFloFld(i + 1, Jtuple.getFloFld(i + 1));
		break;
	case AttrType.attrString:
		JtopTuple.setStrFld(i + 1, Jtuple.getStrFld(i + 1));
		break;
	default:
		throw new UnknowAttrType(
				"Don't know how to handle attrSymbol, attrNull");
	}
}
JtopTuple.setFloFld(nOutFlds + 1, Jtuple.getScore());
return;
}
  
 
  public void get_topK( ) {
		short attrLength = (short) JtopTuple.attr_Types.length;
		FldSpec[] tProjection = new FldSpec[attrLength + 1];
		for (int i = 0; i < attrLength; i++)
			tProjection[i] = new FldSpec(new RelSpec(RelSpec.outer), i + 1);
		FileScan fm1 = null;
		try {
			fm1 = new FileScan("TopNestedLoop.in", JtopTuple.attr_Types,Jtuple.string_sizes, attrLength, attrLength, tProjection,null);
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
		TupleOrder descending = new TupleOrder(TupleOrder.Descending);
		Iterator topIterator = null;
		try {
			//topIterator = new Sort(JtopTuple.attr_Types, (short)1, Jtuple.string_sizes, (iterator.Iterator) this,  1, descending, 4, 5);
			topIterator = new Sort(JtopTuple.attr_Types, attrLength, Jtuple.string_sizes, fm1,  nOutFlds + 1, descending, 4, 5);			
			//topIterator = new Sort(JtopTuple.attr_Types, attrLength,Jtuple.string_sizes, fm1, nOutFlds + 1, descending, 4, 5);
		} catch (SortException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		Tuple tuple1;
		//topK=0;
		while (topK > 0) {
			//topK--;
			try {
				//System.out.println("topK values is  "+topK);
				if ((tuple1 = topIterator.get_next()) != null) {
					tuple1.print(JtopTuple.attr_Types);
					//System.out.println("TOPNESTED SCORE "+tuple1.getScore());
				}
				else{
					System.out.println("no print ");
				}
				//System.out.println("test");
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

  
  
  
  
}