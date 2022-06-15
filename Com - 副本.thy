section "ReqCom --- The Commmand of Regrexp Expressions"

theory Com imports Areg begin

datatype 'a com = SKIP 
      | Match "'a option"  "'a option regexp" nat        
      | Search "'a option regexp" "'a option" nat       
      | Replace "'a option regexp" "'a option" "'a option"     
      | Split "'a option regexp" "'a option" "'a option list"    
      | Extract "'a option" nat 

end