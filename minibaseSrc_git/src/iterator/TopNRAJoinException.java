package iterator;

import chainexception.ChainException;

public class TopNRAJoinException extends ChainException{

	public TopNRAJoinException(String s){super(null,s);}
	  public TopNRAJoinException(Exception prev, String s){ super(prev,s);}

}
