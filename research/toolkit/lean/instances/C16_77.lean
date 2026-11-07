import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 77 of the cap-16 certificate: slots 78848 .. 79871 -/
theorem chk_77 : chunkCheck 16 T stdSt 78848 1024 = true := by decide +kernel

end Row16
