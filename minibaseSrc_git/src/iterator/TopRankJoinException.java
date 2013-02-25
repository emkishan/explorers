package iterator;

import chainexception.*;
import java.lang.*;

public class TopRankJoinException extends ChainException {
  public TopRankJoinException(String s){super(null,s);}
  public TopRankJoinException(Exception prev, String s){ super(prev,s);}
}
