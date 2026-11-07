import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 43 of the cap-16 certificate: slots 44032 .. 45055 -/
theorem chk_43 : chunkCheck 16 T stdSt 44032 1024 = true := by decide +kernel

end Row16
