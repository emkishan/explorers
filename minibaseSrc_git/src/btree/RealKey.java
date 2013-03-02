package btree;

/**  RealKey: It extends the KeyClass.
 *   It defines the real Key.
 */ 
public class RealKey extends KeyClass{

	private float key;

	   /** Class constructor
	   *  @param     s   the value of the string key to be set 
	   */
	  public RealKey(float s) { key = s; }

	  /** get a copy of the real key
	  *  @return the reference of the copy 
	  */ 
	  public float getKey() {return key;}

	  /** set the string key value
	   */ 
	  public void setKey(float s) { key=s;}

}
