package global;

import java.text.SimpleDateFormat;
import java.util.Date;

import java.io.*;

//Apache POI - HSSF imports
import org.apache.poi.hssf.usermodel.HSSFCell;
import org.apache.poi.hssf.usermodel.HSSFDateUtil;
import org.apache.poi.hssf.usermodel.HSSFSheet;
import org.apache.poi.hssf.usermodel.HSSFRow;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.poifs.filesystem.POIFSFileSystem;


public class ExcelParser {

	HSSFSheet m_sheet;
	int m_iNbRows;
	int m_iNbColms =0;
	int m_iCurrentRow = 0;
    private static final String JAVA_TOSTRING =
 "EEE MMM dd HH:mm:ss zzz yyyy";
    
     
	
	public ExcelParser(HSSFSheet sheet)
	{
		m_sheet = sheet;
		m_iNbRows = sheet.getPhysicalNumberOfRows();
				
	}
	
	public int getNumberOfColms(){
		//System.out.println("noOfColms ="+m_iNbColms);
		String res[];
		try {
			while ((res = splitLine()) != null)
			{
				
			}
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		System.out.println("Colms ="+m_iNbColms);
		return m_iNbColms;
	}
	
	
	/* Returns the contents of an Excel row in the 
form of a String array.
	 * @see com.ibm.ccd.common.parsing.Parser#splitLine()
	 */
	public String[] splitLine() throws Exception {
		if (m_iCurrentRow == m_iNbRows)
			return null;
		
		HSSFRow row = m_sheet.getRow(m_iCurrentRow);
		if(row == null)
		{
			return null;
		}
		else
		{
			int cellIndex = 0; 
			int noOfCells =	row.getPhysicalNumberOfCells();
			System.out.println("noOfCell ="+noOfCells);
			String[] values = new String[noOfCells];        
			short firstCellNum = row.getFirstCellNum();
			short lastCellNum = row.getLastCellNum();
			System.out.println("getRowNum ="+row.getRowNum());
			if (firstCellNum >=0 && lastCellNum >=0) 
			{
				for(short iCurrent = firstCellNum; iCurrent <lastCellNum; iCurrent++) 
			{
					HSSFCell cell = (HSSFCell)row.getCell(iCurrent);
					if(cell == null)
					{
						values[iCurrent] = "";
						cellIndex++;        		
						continue;
					}
					else
					{
						if(row.getRowNum()==0){
							m_iNbColms ++;
						}
						//System.out.println(cell.getNumericCellValue());
						switch(cell.getCellType())
						{   
						
						case HSSFCell.CELL_TYPE_NUMERIC:
						double value = cell.getNumericCellValue();
						//System.out.println("value1="+value);
																		
						if(HSSFDateUtil.isCellDateFormatted(cell)) 
								
						{
							if(HSSFDateUtil.isValidExcelDate(value))
							{
								Date date = HSSFDateUtil.getJavaDate(value);
								SimpleDateFormat dateFormat = new SimpleDateFormat(JAVA_TOSTRING);	
								values[iCurrent] = dateFormat.format(date);								
							}
							else
							{
								throw new Exception("Invalid Date value found at row number " +
										row.getRowNum()+" and column number "+cell.getCellNum());	
							}
						}
						else
						{
							int valueInt;
							if(value%1==0)
							{
								valueInt= (int) value;
								//System.out.println("value2="+valueInt);
								values[iCurrent] = valueInt + "";
							}
							else
							{
							values[iCurrent] = value + "";
							//System.out.println("value3="+value);
							}
						}
						break;
						
						case HSSFCell.CELL_TYPE_STRING:
							values[iCurrent] = cell.getStringCellValue();
						break;
						
						case HSSFCell.CELL_TYPE_BLANK:
							values[iCurrent] = null;	
						break;
						
						default:
							values[iCurrent] = null;	
						}        	
					}        	            	
				}        
			}
			m_iCurrentRow++;
			/*for(int j=0;j<values.length;j++)
				System.out.println("Inside "+values[j]);*/
			return values;	            
		}
		
	}

   public static void main(String args[])
   {
       HSSFWorkbook workBook = null; 
       File file  = new File("C:/ExcelTest/ExcelTest3.xls");
       InputStream excelDocumentStream = null;
       try 
       {
           excelDocumentStream = new FileInputStream(file);
           POIFSFileSystem fsPOI = new POIFSFileSystem(new BufferedInputStream(excelDocumentStream));
           workBook = new HSSFWorkbook(fsPOI);         
           ExcelParser parser = new ExcelParser(workBook.getSheetAt(0));
           String [] res;
           parser.getNumberOfColms();
            while ((res = parser.splitLine()) != null)
            {
							for (int i = 0; i < res.length; i++)
                {
                    System.out.println("Token Found [" + res[i] + "]");
                }
            }
            excelDocumentStream.close();
            //System.out.println("noOfColms ="+parser.getNumberOfColms());
        }
        catch(Exception e)
        {
            e.printStackTrace();
        }

        
   }

}
