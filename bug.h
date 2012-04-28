import qualified Bug as Bug_

#define hcBug (\imp_funny_name -> imp_funny_name (__FILE__,__LINE__,__TIME__,__DATE__))

#define bug        (hcBug Bug_._bug)
#define impossible (hcBug Bug_._impossible)
#define fromJust   (hcBug Bug_._fromJust)
#define bugDoc     (hcBug Bug_._bugDoc)
