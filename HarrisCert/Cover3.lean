module

public import HarrisCert.Kernel
public import HarrisCert.Leaves.L32
public import HarrisCert.Leaves.L33
public import HarrisCert.Leaves.L34
public import HarrisCert.Leaves.L35
public import HarrisCert.Leaves.L36
public import HarrisCert.Leaves.L37
public import HarrisCert.Leaves.L38
public import HarrisCert.Leaves.L39
public import HarrisCert.Leaves.L40
public import HarrisCert.Leaves.L41
public import HarrisCert.Leaves.L42
public import HarrisCert.Leaves.L43

/-! Leaves 1970 … 2626 cover their boxes. -/

@[expose] public section

namespace Harris

theorem cr_1970_1971 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 1971) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1970 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1970_ok
theorem cr_1971_1972 (k : ℕ) (h1 : 1971 ≤ k) (h2 : k < 1972) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1971 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1971_ok
theorem cr_1970_1972 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 1972) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1971 then cr_1970_1971 k h1 h else cr_1971_1972 k (by omega) h2
theorem cr_1972_1973 (k : ℕ) (h1 : 1972 ≤ k) (h2 : k < 1973) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1972 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1972_ok
theorem cr_1973_1974 (k : ℕ) (h1 : 1973 ≤ k) (h2 : k < 1974) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1973 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1973_ok
theorem cr_1974_1975 (k : ℕ) (h1 : 1974 ≤ k) (h2 : k < 1975) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1974 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1974_ok
theorem cr_1973_1975 (k : ℕ) (h1 : 1973 ≤ k) (h2 : k < 1975) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1974 then cr_1973_1974 k h1 h else cr_1974_1975 k (by omega) h2
theorem cr_1972_1975 (k : ℕ) (h1 : 1972 ≤ k) (h2 : k < 1975) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1973 then cr_1972_1973 k h1 h else cr_1973_1975 k (by omega) h2
theorem cr_1970_1975 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 1975) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1972 then cr_1970_1972 k h1 h else cr_1972_1975 k (by omega) h2
theorem cr_1975_1976 (k : ℕ) (h1 : 1975 ≤ k) (h2 : k < 1976) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1975 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1975_ok
theorem cr_1976_1977 (k : ℕ) (h1 : 1976 ≤ k) (h2 : k < 1977) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1976 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1976_ok
theorem cr_1975_1977 (k : ℕ) (h1 : 1975 ≤ k) (h2 : k < 1977) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1976 then cr_1975_1976 k h1 h else cr_1976_1977 k (by omega) h2
theorem cr_1977_1978 (k : ℕ) (h1 : 1977 ≤ k) (h2 : k < 1978) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1977 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1977_ok
theorem cr_1978_1979 (k : ℕ) (h1 : 1978 ≤ k) (h2 : k < 1979) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1978 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1978_ok
theorem cr_1979_1980 (k : ℕ) (h1 : 1979 ≤ k) (h2 : k < 1980) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1979 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1979_ok
theorem cr_1978_1980 (k : ℕ) (h1 : 1978 ≤ k) (h2 : k < 1980) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1979 then cr_1978_1979 k h1 h else cr_1979_1980 k (by omega) h2
theorem cr_1977_1980 (k : ℕ) (h1 : 1977 ≤ k) (h2 : k < 1980) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1978 then cr_1977_1978 k h1 h else cr_1978_1980 k (by omega) h2
theorem cr_1975_1980 (k : ℕ) (h1 : 1975 ≤ k) (h2 : k < 1980) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1977 then cr_1975_1977 k h1 h else cr_1977_1980 k (by omega) h2
theorem cr_1970_1980 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 1980) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1975 then cr_1970_1975 k h1 h else cr_1975_1980 k (by omega) h2
theorem cr_1980_1981 (k : ℕ) (h1 : 1980 ≤ k) (h2 : k < 1981) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1980 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1980_ok
theorem cr_1981_1982 (k : ℕ) (h1 : 1981 ≤ k) (h2 : k < 1982) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1981 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1981_ok
theorem cr_1980_1982 (k : ℕ) (h1 : 1980 ≤ k) (h2 : k < 1982) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1981 then cr_1980_1981 k h1 h else cr_1981_1982 k (by omega) h2
theorem cr_1982_1983 (k : ℕ) (h1 : 1982 ≤ k) (h2 : k < 1983) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1982 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1982_ok
theorem cr_1983_1984 (k : ℕ) (h1 : 1983 ≤ k) (h2 : k < 1984) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1983 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1983_ok
theorem cr_1984_1985 (k : ℕ) (h1 : 1984 ≤ k) (h2 : k < 1985) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1984 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1984_ok
theorem cr_1983_1985 (k : ℕ) (h1 : 1983 ≤ k) (h2 : k < 1985) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1984 then cr_1983_1984 k h1 h else cr_1984_1985 k (by omega) h2
theorem cr_1982_1985 (k : ℕ) (h1 : 1982 ≤ k) (h2 : k < 1985) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1983 then cr_1982_1983 k h1 h else cr_1983_1985 k (by omega) h2
theorem cr_1980_1985 (k : ℕ) (h1 : 1980 ≤ k) (h2 : k < 1985) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1982 then cr_1980_1982 k h1 h else cr_1982_1985 k (by omega) h2
theorem cr_1985_1986 (k : ℕ) (h1 : 1985 ≤ k) (h2 : k < 1986) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1985 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1985_ok
theorem cr_1986_1987 (k : ℕ) (h1 : 1986 ≤ k) (h2 : k < 1987) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1986 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1986_ok
theorem cr_1985_1987 (k : ℕ) (h1 : 1985 ≤ k) (h2 : k < 1987) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1986 then cr_1985_1986 k h1 h else cr_1986_1987 k (by omega) h2
theorem cr_1987_1988 (k : ℕ) (h1 : 1987 ≤ k) (h2 : k < 1988) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1987 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1987_ok
theorem cr_1988_1989 (k : ℕ) (h1 : 1988 ≤ k) (h2 : k < 1989) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1988 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1988_ok
theorem cr_1989_1990 (k : ℕ) (h1 : 1989 ≤ k) (h2 : k < 1990) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1989 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1989_ok
theorem cr_1988_1990 (k : ℕ) (h1 : 1988 ≤ k) (h2 : k < 1990) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1989 then cr_1988_1989 k h1 h else cr_1989_1990 k (by omega) h2
theorem cr_1987_1990 (k : ℕ) (h1 : 1987 ≤ k) (h2 : k < 1990) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1988 then cr_1987_1988 k h1 h else cr_1988_1990 k (by omega) h2
theorem cr_1985_1990 (k : ℕ) (h1 : 1985 ≤ k) (h2 : k < 1990) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1987 then cr_1985_1987 k h1 h else cr_1987_1990 k (by omega) h2
theorem cr_1980_1990 (k : ℕ) (h1 : 1980 ≤ k) (h2 : k < 1990) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1985 then cr_1980_1985 k h1 h else cr_1985_1990 k (by omega) h2
theorem cr_1970_1990 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 1990) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1980 then cr_1970_1980 k h1 h else cr_1980_1990 k (by omega) h2
theorem cr_1990_1991 (k : ℕ) (h1 : 1990 ≤ k) (h2 : k < 1991) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1990 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1990_ok
theorem cr_1991_1992 (k : ℕ) (h1 : 1991 ≤ k) (h2 : k < 1992) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1991 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1991_ok
theorem cr_1990_1992 (k : ℕ) (h1 : 1990 ≤ k) (h2 : k < 1992) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1991 then cr_1990_1991 k h1 h else cr_1991_1992 k (by omega) h2
theorem cr_1992_1993 (k : ℕ) (h1 : 1992 ≤ k) (h2 : k < 1993) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1992 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1992_ok
theorem cr_1993_1994 (k : ℕ) (h1 : 1993 ≤ k) (h2 : k < 1994) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1993 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1993_ok
theorem cr_1994_1995 (k : ℕ) (h1 : 1994 ≤ k) (h2 : k < 1995) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1994 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1994_ok
theorem cr_1993_1995 (k : ℕ) (h1 : 1993 ≤ k) (h2 : k < 1995) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1994 then cr_1993_1994 k h1 h else cr_1994_1995 k (by omega) h2
theorem cr_1992_1995 (k : ℕ) (h1 : 1992 ≤ k) (h2 : k < 1995) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1993 then cr_1992_1993 k h1 h else cr_1993_1995 k (by omega) h2
theorem cr_1990_1995 (k : ℕ) (h1 : 1990 ≤ k) (h2 : k < 1995) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1992 then cr_1990_1992 k h1 h else cr_1992_1995 k (by omega) h2
theorem cr_1995_1996 (k : ℕ) (h1 : 1995 ≤ k) (h2 : k < 1996) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1995 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1995_ok
theorem cr_1996_1997 (k : ℕ) (h1 : 1996 ≤ k) (h2 : k < 1997) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1996 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1996_ok
theorem cr_1995_1997 (k : ℕ) (h1 : 1995 ≤ k) (h2 : k < 1997) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1996 then cr_1995_1996 k h1 h else cr_1996_1997 k (by omega) h2
theorem cr_1997_1998 (k : ℕ) (h1 : 1997 ≤ k) (h2 : k < 1998) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1997 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1997_ok
theorem cr_1998_1999 (k : ℕ) (h1 : 1998 ≤ k) (h2 : k < 1999) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1998 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1998_ok
theorem cr_1999_2000 (k : ℕ) (h1 : 1999 ≤ k) (h2 : k < 2000) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 1999 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf1999_ok
theorem cr_1998_2000 (k : ℕ) (h1 : 1998 ≤ k) (h2 : k < 2000) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1999 then cr_1998_1999 k h1 h else cr_1999_2000 k (by omega) h2
theorem cr_1997_2000 (k : ℕ) (h1 : 1997 ≤ k) (h2 : k < 2000) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1998 then cr_1997_1998 k h1 h else cr_1998_2000 k (by omega) h2
theorem cr_1995_2000 (k : ℕ) (h1 : 1995 ≤ k) (h2 : k < 2000) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1997 then cr_1995_1997 k h1 h else cr_1997_2000 k (by omega) h2
theorem cr_1990_2000 (k : ℕ) (h1 : 1990 ≤ k) (h2 : k < 2000) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1995 then cr_1990_1995 k h1 h else cr_1995_2000 k (by omega) h2
theorem cr_2000_2001 (k : ℕ) (h1 : 2000 ≤ k) (h2 : k < 2001) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2000 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2000_ok
theorem cr_2001_2002 (k : ℕ) (h1 : 2001 ≤ k) (h2 : k < 2002) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2001 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2001_ok
theorem cr_2000_2002 (k : ℕ) (h1 : 2000 ≤ k) (h2 : k < 2002) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2001 then cr_2000_2001 k h1 h else cr_2001_2002 k (by omega) h2
theorem cr_2002_2003 (k : ℕ) (h1 : 2002 ≤ k) (h2 : k < 2003) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2002 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2002_ok
theorem cr_2003_2004 (k : ℕ) (h1 : 2003 ≤ k) (h2 : k < 2004) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2003 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2003_ok
theorem cr_2004_2005 (k : ℕ) (h1 : 2004 ≤ k) (h2 : k < 2005) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2004 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2004_ok
theorem cr_2003_2005 (k : ℕ) (h1 : 2003 ≤ k) (h2 : k < 2005) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2004 then cr_2003_2004 k h1 h else cr_2004_2005 k (by omega) h2
theorem cr_2002_2005 (k : ℕ) (h1 : 2002 ≤ k) (h2 : k < 2005) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2003 then cr_2002_2003 k h1 h else cr_2003_2005 k (by omega) h2
theorem cr_2000_2005 (k : ℕ) (h1 : 2000 ≤ k) (h2 : k < 2005) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2002 then cr_2000_2002 k h1 h else cr_2002_2005 k (by omega) h2
theorem cr_2005_2006 (k : ℕ) (h1 : 2005 ≤ k) (h2 : k < 2006) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2005 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2005_ok
theorem cr_2006_2007 (k : ℕ) (h1 : 2006 ≤ k) (h2 : k < 2007) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2006 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2006_ok
theorem cr_2007_2008 (k : ℕ) (h1 : 2007 ≤ k) (h2 : k < 2008) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2007 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2007_ok
theorem cr_2006_2008 (k : ℕ) (h1 : 2006 ≤ k) (h2 : k < 2008) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2007 then cr_2006_2007 k h1 h else cr_2007_2008 k (by omega) h2
theorem cr_2005_2008 (k : ℕ) (h1 : 2005 ≤ k) (h2 : k < 2008) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2006 then cr_2005_2006 k h1 h else cr_2006_2008 k (by omega) h2
theorem cr_2008_2009 (k : ℕ) (h1 : 2008 ≤ k) (h2 : k < 2009) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2008 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2008_ok
theorem cr_2009_2010 (k : ℕ) (h1 : 2009 ≤ k) (h2 : k < 2010) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2009 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2009_ok
theorem cr_2010_2011 (k : ℕ) (h1 : 2010 ≤ k) (h2 : k < 2011) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2010 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2010_ok
theorem cr_2009_2011 (k : ℕ) (h1 : 2009 ≤ k) (h2 : k < 2011) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2010 then cr_2009_2010 k h1 h else cr_2010_2011 k (by omega) h2
theorem cr_2008_2011 (k : ℕ) (h1 : 2008 ≤ k) (h2 : k < 2011) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2009 then cr_2008_2009 k h1 h else cr_2009_2011 k (by omega) h2
theorem cr_2005_2011 (k : ℕ) (h1 : 2005 ≤ k) (h2 : k < 2011) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2008 then cr_2005_2008 k h1 h else cr_2008_2011 k (by omega) h2
theorem cr_2000_2011 (k : ℕ) (h1 : 2000 ≤ k) (h2 : k < 2011) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2005 then cr_2000_2005 k h1 h else cr_2005_2011 k (by omega) h2
theorem cr_1990_2011 (k : ℕ) (h1 : 1990 ≤ k) (h2 : k < 2011) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2000 then cr_1990_2000 k h1 h else cr_2000_2011 k (by omega) h2
theorem cr_1970_2011 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 2011) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 1990 then cr_1970_1990 k h1 h else cr_1990_2011 k (by omega) h2
theorem cr_2011_2012 (k : ℕ) (h1 : 2011 ≤ k) (h2 : k < 2012) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2011 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2011_ok
theorem cr_2012_2013 (k : ℕ) (h1 : 2012 ≤ k) (h2 : k < 2013) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2012 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2012_ok
theorem cr_2011_2013 (k : ℕ) (h1 : 2011 ≤ k) (h2 : k < 2013) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2012 then cr_2011_2012 k h1 h else cr_2012_2013 k (by omega) h2
theorem cr_2013_2014 (k : ℕ) (h1 : 2013 ≤ k) (h2 : k < 2014) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2013 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2013_ok
theorem cr_2014_2015 (k : ℕ) (h1 : 2014 ≤ k) (h2 : k < 2015) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2014 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2014_ok
theorem cr_2015_2016 (k : ℕ) (h1 : 2015 ≤ k) (h2 : k < 2016) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2015 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2015_ok
theorem cr_2014_2016 (k : ℕ) (h1 : 2014 ≤ k) (h2 : k < 2016) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2015 then cr_2014_2015 k h1 h else cr_2015_2016 k (by omega) h2
theorem cr_2013_2016 (k : ℕ) (h1 : 2013 ≤ k) (h2 : k < 2016) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2014 then cr_2013_2014 k h1 h else cr_2014_2016 k (by omega) h2
theorem cr_2011_2016 (k : ℕ) (h1 : 2011 ≤ k) (h2 : k < 2016) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2013 then cr_2011_2013 k h1 h else cr_2013_2016 k (by omega) h2
theorem cr_2016_2017 (k : ℕ) (h1 : 2016 ≤ k) (h2 : k < 2017) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2016 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2016_ok
theorem cr_2017_2018 (k : ℕ) (h1 : 2017 ≤ k) (h2 : k < 2018) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2017 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2017_ok
theorem cr_2016_2018 (k : ℕ) (h1 : 2016 ≤ k) (h2 : k < 2018) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2017 then cr_2016_2017 k h1 h else cr_2017_2018 k (by omega) h2
theorem cr_2018_2019 (k : ℕ) (h1 : 2018 ≤ k) (h2 : k < 2019) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2018 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2018_ok
theorem cr_2019_2020 (k : ℕ) (h1 : 2019 ≤ k) (h2 : k < 2020) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2019 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2019_ok
theorem cr_2020_2021 (k : ℕ) (h1 : 2020 ≤ k) (h2 : k < 2021) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2020 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2020_ok
theorem cr_2019_2021 (k : ℕ) (h1 : 2019 ≤ k) (h2 : k < 2021) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2020 then cr_2019_2020 k h1 h else cr_2020_2021 k (by omega) h2
theorem cr_2018_2021 (k : ℕ) (h1 : 2018 ≤ k) (h2 : k < 2021) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2019 then cr_2018_2019 k h1 h else cr_2019_2021 k (by omega) h2
theorem cr_2016_2021 (k : ℕ) (h1 : 2016 ≤ k) (h2 : k < 2021) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2018 then cr_2016_2018 k h1 h else cr_2018_2021 k (by omega) h2
theorem cr_2011_2021 (k : ℕ) (h1 : 2011 ≤ k) (h2 : k < 2021) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2016 then cr_2011_2016 k h1 h else cr_2016_2021 k (by omega) h2
theorem cr_2021_2022 (k : ℕ) (h1 : 2021 ≤ k) (h2 : k < 2022) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2021 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2021_ok
theorem cr_2022_2023 (k : ℕ) (h1 : 2022 ≤ k) (h2 : k < 2023) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2022 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2022_ok
theorem cr_2021_2023 (k : ℕ) (h1 : 2021 ≤ k) (h2 : k < 2023) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2022 then cr_2021_2022 k h1 h else cr_2022_2023 k (by omega) h2
theorem cr_2023_2024 (k : ℕ) (h1 : 2023 ≤ k) (h2 : k < 2024) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2023 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2023_ok
theorem cr_2024_2025 (k : ℕ) (h1 : 2024 ≤ k) (h2 : k < 2025) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2024 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2024_ok
theorem cr_2025_2026 (k : ℕ) (h1 : 2025 ≤ k) (h2 : k < 2026) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2025 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2025_ok
theorem cr_2024_2026 (k : ℕ) (h1 : 2024 ≤ k) (h2 : k < 2026) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2025 then cr_2024_2025 k h1 h else cr_2025_2026 k (by omega) h2
theorem cr_2023_2026 (k : ℕ) (h1 : 2023 ≤ k) (h2 : k < 2026) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2024 then cr_2023_2024 k h1 h else cr_2024_2026 k (by omega) h2
theorem cr_2021_2026 (k : ℕ) (h1 : 2021 ≤ k) (h2 : k < 2026) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2023 then cr_2021_2023 k h1 h else cr_2023_2026 k (by omega) h2
theorem cr_2026_2027 (k : ℕ) (h1 : 2026 ≤ k) (h2 : k < 2027) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2026 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2026_ok
theorem cr_2027_2028 (k : ℕ) (h1 : 2027 ≤ k) (h2 : k < 2028) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2027 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2027_ok
theorem cr_2026_2028 (k : ℕ) (h1 : 2026 ≤ k) (h2 : k < 2028) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2027 then cr_2026_2027 k h1 h else cr_2027_2028 k (by omega) h2
theorem cr_2028_2029 (k : ℕ) (h1 : 2028 ≤ k) (h2 : k < 2029) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2028 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2028_ok
theorem cr_2029_2030 (k : ℕ) (h1 : 2029 ≤ k) (h2 : k < 2030) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2029 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2029_ok
theorem cr_2030_2031 (k : ℕ) (h1 : 2030 ≤ k) (h2 : k < 2031) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2030 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2030_ok
theorem cr_2029_2031 (k : ℕ) (h1 : 2029 ≤ k) (h2 : k < 2031) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2030 then cr_2029_2030 k h1 h else cr_2030_2031 k (by omega) h2
theorem cr_2028_2031 (k : ℕ) (h1 : 2028 ≤ k) (h2 : k < 2031) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2029 then cr_2028_2029 k h1 h else cr_2029_2031 k (by omega) h2
theorem cr_2026_2031 (k : ℕ) (h1 : 2026 ≤ k) (h2 : k < 2031) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2028 then cr_2026_2028 k h1 h else cr_2028_2031 k (by omega) h2
theorem cr_2021_2031 (k : ℕ) (h1 : 2021 ≤ k) (h2 : k < 2031) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2026 then cr_2021_2026 k h1 h else cr_2026_2031 k (by omega) h2
theorem cr_2011_2031 (k : ℕ) (h1 : 2011 ≤ k) (h2 : k < 2031) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2021 then cr_2011_2021 k h1 h else cr_2021_2031 k (by omega) h2
theorem cr_2031_2032 (k : ℕ) (h1 : 2031 ≤ k) (h2 : k < 2032) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2031 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2031_ok
theorem cr_2032_2033 (k : ℕ) (h1 : 2032 ≤ k) (h2 : k < 2033) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2032 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2032_ok
theorem cr_2031_2033 (k : ℕ) (h1 : 2031 ≤ k) (h2 : k < 2033) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2032 then cr_2031_2032 k h1 h else cr_2032_2033 k (by omega) h2
theorem cr_2033_2034 (k : ℕ) (h1 : 2033 ≤ k) (h2 : k < 2034) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2033 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2033_ok
theorem cr_2034_2035 (k : ℕ) (h1 : 2034 ≤ k) (h2 : k < 2035) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2034 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2034_ok
theorem cr_2035_2036 (k : ℕ) (h1 : 2035 ≤ k) (h2 : k < 2036) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2035 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2035_ok
theorem cr_2034_2036 (k : ℕ) (h1 : 2034 ≤ k) (h2 : k < 2036) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2035 then cr_2034_2035 k h1 h else cr_2035_2036 k (by omega) h2
theorem cr_2033_2036 (k : ℕ) (h1 : 2033 ≤ k) (h2 : k < 2036) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2034 then cr_2033_2034 k h1 h else cr_2034_2036 k (by omega) h2
theorem cr_2031_2036 (k : ℕ) (h1 : 2031 ≤ k) (h2 : k < 2036) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2033 then cr_2031_2033 k h1 h else cr_2033_2036 k (by omega) h2
theorem cr_2036_2037 (k : ℕ) (h1 : 2036 ≤ k) (h2 : k < 2037) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2036 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2036_ok
theorem cr_2037_2038 (k : ℕ) (h1 : 2037 ≤ k) (h2 : k < 2038) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2037 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2037_ok
theorem cr_2036_2038 (k : ℕ) (h1 : 2036 ≤ k) (h2 : k < 2038) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2037 then cr_2036_2037 k h1 h else cr_2037_2038 k (by omega) h2
theorem cr_2038_2039 (k : ℕ) (h1 : 2038 ≤ k) (h2 : k < 2039) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2038 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2038_ok
theorem cr_2039_2040 (k : ℕ) (h1 : 2039 ≤ k) (h2 : k < 2040) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2039 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2039_ok
theorem cr_2040_2041 (k : ℕ) (h1 : 2040 ≤ k) (h2 : k < 2041) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2040 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2040_ok
theorem cr_2039_2041 (k : ℕ) (h1 : 2039 ≤ k) (h2 : k < 2041) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2040 then cr_2039_2040 k h1 h else cr_2040_2041 k (by omega) h2
theorem cr_2038_2041 (k : ℕ) (h1 : 2038 ≤ k) (h2 : k < 2041) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2039 then cr_2038_2039 k h1 h else cr_2039_2041 k (by omega) h2
theorem cr_2036_2041 (k : ℕ) (h1 : 2036 ≤ k) (h2 : k < 2041) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2038 then cr_2036_2038 k h1 h else cr_2038_2041 k (by omega) h2
theorem cr_2031_2041 (k : ℕ) (h1 : 2031 ≤ k) (h2 : k < 2041) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2036 then cr_2031_2036 k h1 h else cr_2036_2041 k (by omega) h2
theorem cr_2041_2042 (k : ℕ) (h1 : 2041 ≤ k) (h2 : k < 2042) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2041 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2041_ok
theorem cr_2042_2043 (k : ℕ) (h1 : 2042 ≤ k) (h2 : k < 2043) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2042 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2042_ok
theorem cr_2041_2043 (k : ℕ) (h1 : 2041 ≤ k) (h2 : k < 2043) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2042 then cr_2041_2042 k h1 h else cr_2042_2043 k (by omega) h2
theorem cr_2043_2044 (k : ℕ) (h1 : 2043 ≤ k) (h2 : k < 2044) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2043 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2043_ok
theorem cr_2044_2045 (k : ℕ) (h1 : 2044 ≤ k) (h2 : k < 2045) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2044 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2044_ok
theorem cr_2045_2046 (k : ℕ) (h1 : 2045 ≤ k) (h2 : k < 2046) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2045 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2045_ok
theorem cr_2044_2046 (k : ℕ) (h1 : 2044 ≤ k) (h2 : k < 2046) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2045 then cr_2044_2045 k h1 h else cr_2045_2046 k (by omega) h2
theorem cr_2043_2046 (k : ℕ) (h1 : 2043 ≤ k) (h2 : k < 2046) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2044 then cr_2043_2044 k h1 h else cr_2044_2046 k (by omega) h2
theorem cr_2041_2046 (k : ℕ) (h1 : 2041 ≤ k) (h2 : k < 2046) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2043 then cr_2041_2043 k h1 h else cr_2043_2046 k (by omega) h2
theorem cr_2046_2047 (k : ℕ) (h1 : 2046 ≤ k) (h2 : k < 2047) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2046 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2046_ok
theorem cr_2047_2048 (k : ℕ) (h1 : 2047 ≤ k) (h2 : k < 2048) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2047 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2047_ok
theorem cr_2048_2049 (k : ℕ) (h1 : 2048 ≤ k) (h2 : k < 2049) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2048 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2048_ok
theorem cr_2047_2049 (k : ℕ) (h1 : 2047 ≤ k) (h2 : k < 2049) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2048 then cr_2047_2048 k h1 h else cr_2048_2049 k (by omega) h2
theorem cr_2046_2049 (k : ℕ) (h1 : 2046 ≤ k) (h2 : k < 2049) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2047 then cr_2046_2047 k h1 h else cr_2047_2049 k (by omega) h2
theorem cr_2049_2050 (k : ℕ) (h1 : 2049 ≤ k) (h2 : k < 2050) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2049 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2049_ok
theorem cr_2050_2051 (k : ℕ) (h1 : 2050 ≤ k) (h2 : k < 2051) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2050 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2050_ok
theorem cr_2051_2052 (k : ℕ) (h1 : 2051 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2051 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2051_ok
theorem cr_2050_2052 (k : ℕ) (h1 : 2050 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2051 then cr_2050_2051 k h1 h else cr_2051_2052 k (by omega) h2
theorem cr_2049_2052 (k : ℕ) (h1 : 2049 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2050 then cr_2049_2050 k h1 h else cr_2050_2052 k (by omega) h2
theorem cr_2046_2052 (k : ℕ) (h1 : 2046 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2049 then cr_2046_2049 k h1 h else cr_2049_2052 k (by omega) h2
theorem cr_2041_2052 (k : ℕ) (h1 : 2041 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2046 then cr_2041_2046 k h1 h else cr_2046_2052 k (by omega) h2
theorem cr_2031_2052 (k : ℕ) (h1 : 2031 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2041 then cr_2031_2041 k h1 h else cr_2041_2052 k (by omega) h2
theorem cr_2011_2052 (k : ℕ) (h1 : 2011 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2031 then cr_2011_2031 k h1 h else cr_2031_2052 k (by omega) h2
theorem cr_1970_2052 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 2052) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2011 then cr_1970_2011 k h1 h else cr_2011_2052 k (by omega) h2
theorem cr_2052_2053 (k : ℕ) (h1 : 2052 ≤ k) (h2 : k < 2053) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2052 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2052_ok
theorem cr_2053_2054 (k : ℕ) (h1 : 2053 ≤ k) (h2 : k < 2054) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2053 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2053_ok
theorem cr_2052_2054 (k : ℕ) (h1 : 2052 ≤ k) (h2 : k < 2054) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2053 then cr_2052_2053 k h1 h else cr_2053_2054 k (by omega) h2
theorem cr_2054_2055 (k : ℕ) (h1 : 2054 ≤ k) (h2 : k < 2055) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2054 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2054_ok
theorem cr_2055_2056 (k : ℕ) (h1 : 2055 ≤ k) (h2 : k < 2056) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2055 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2055_ok
theorem cr_2056_2057 (k : ℕ) (h1 : 2056 ≤ k) (h2 : k < 2057) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2056 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2056_ok
theorem cr_2055_2057 (k : ℕ) (h1 : 2055 ≤ k) (h2 : k < 2057) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2056 then cr_2055_2056 k h1 h else cr_2056_2057 k (by omega) h2
theorem cr_2054_2057 (k : ℕ) (h1 : 2054 ≤ k) (h2 : k < 2057) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2055 then cr_2054_2055 k h1 h else cr_2055_2057 k (by omega) h2
theorem cr_2052_2057 (k : ℕ) (h1 : 2052 ≤ k) (h2 : k < 2057) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2054 then cr_2052_2054 k h1 h else cr_2054_2057 k (by omega) h2
theorem cr_2057_2058 (k : ℕ) (h1 : 2057 ≤ k) (h2 : k < 2058) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2057 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2057_ok
theorem cr_2058_2059 (k : ℕ) (h1 : 2058 ≤ k) (h2 : k < 2059) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2058 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2058_ok
theorem cr_2057_2059 (k : ℕ) (h1 : 2057 ≤ k) (h2 : k < 2059) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2058 then cr_2057_2058 k h1 h else cr_2058_2059 k (by omega) h2
theorem cr_2059_2060 (k : ℕ) (h1 : 2059 ≤ k) (h2 : k < 2060) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2059 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2059_ok
theorem cr_2060_2061 (k : ℕ) (h1 : 2060 ≤ k) (h2 : k < 2061) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2060 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2060_ok
theorem cr_2061_2062 (k : ℕ) (h1 : 2061 ≤ k) (h2 : k < 2062) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2061 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2061_ok
theorem cr_2060_2062 (k : ℕ) (h1 : 2060 ≤ k) (h2 : k < 2062) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2061 then cr_2060_2061 k h1 h else cr_2061_2062 k (by omega) h2
theorem cr_2059_2062 (k : ℕ) (h1 : 2059 ≤ k) (h2 : k < 2062) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2060 then cr_2059_2060 k h1 h else cr_2060_2062 k (by omega) h2
theorem cr_2057_2062 (k : ℕ) (h1 : 2057 ≤ k) (h2 : k < 2062) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2059 then cr_2057_2059 k h1 h else cr_2059_2062 k (by omega) h2
theorem cr_2052_2062 (k : ℕ) (h1 : 2052 ≤ k) (h2 : k < 2062) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2057 then cr_2052_2057 k h1 h else cr_2057_2062 k (by omega) h2
theorem cr_2062_2063 (k : ℕ) (h1 : 2062 ≤ k) (h2 : k < 2063) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2062 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2062_ok
theorem cr_2063_2064 (k : ℕ) (h1 : 2063 ≤ k) (h2 : k < 2064) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2063 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2063_ok
theorem cr_2062_2064 (k : ℕ) (h1 : 2062 ≤ k) (h2 : k < 2064) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2063 then cr_2062_2063 k h1 h else cr_2063_2064 k (by omega) h2
theorem cr_2064_2065 (k : ℕ) (h1 : 2064 ≤ k) (h2 : k < 2065) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2064 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2064_ok
theorem cr_2065_2066 (k : ℕ) (h1 : 2065 ≤ k) (h2 : k < 2066) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2065 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2065_ok
theorem cr_2066_2067 (k : ℕ) (h1 : 2066 ≤ k) (h2 : k < 2067) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2066 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2066_ok
theorem cr_2065_2067 (k : ℕ) (h1 : 2065 ≤ k) (h2 : k < 2067) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2066 then cr_2065_2066 k h1 h else cr_2066_2067 k (by omega) h2
theorem cr_2064_2067 (k : ℕ) (h1 : 2064 ≤ k) (h2 : k < 2067) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2065 then cr_2064_2065 k h1 h else cr_2065_2067 k (by omega) h2
theorem cr_2062_2067 (k : ℕ) (h1 : 2062 ≤ k) (h2 : k < 2067) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2064 then cr_2062_2064 k h1 h else cr_2064_2067 k (by omega) h2
theorem cr_2067_2068 (k : ℕ) (h1 : 2067 ≤ k) (h2 : k < 2068) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2067 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2067_ok
theorem cr_2068_2069 (k : ℕ) (h1 : 2068 ≤ k) (h2 : k < 2069) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2068 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2068_ok
theorem cr_2067_2069 (k : ℕ) (h1 : 2067 ≤ k) (h2 : k < 2069) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2068 then cr_2067_2068 k h1 h else cr_2068_2069 k (by omega) h2
theorem cr_2069_2070 (k : ℕ) (h1 : 2069 ≤ k) (h2 : k < 2070) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2069 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2069_ok
theorem cr_2070_2071 (k : ℕ) (h1 : 2070 ≤ k) (h2 : k < 2071) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2070 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2070_ok
theorem cr_2071_2072 (k : ℕ) (h1 : 2071 ≤ k) (h2 : k < 2072) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2071 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2071_ok
theorem cr_2070_2072 (k : ℕ) (h1 : 2070 ≤ k) (h2 : k < 2072) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2071 then cr_2070_2071 k h1 h else cr_2071_2072 k (by omega) h2
theorem cr_2069_2072 (k : ℕ) (h1 : 2069 ≤ k) (h2 : k < 2072) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2070 then cr_2069_2070 k h1 h else cr_2070_2072 k (by omega) h2
theorem cr_2067_2072 (k : ℕ) (h1 : 2067 ≤ k) (h2 : k < 2072) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2069 then cr_2067_2069 k h1 h else cr_2069_2072 k (by omega) h2
theorem cr_2062_2072 (k : ℕ) (h1 : 2062 ≤ k) (h2 : k < 2072) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2067 then cr_2062_2067 k h1 h else cr_2067_2072 k (by omega) h2
theorem cr_2052_2072 (k : ℕ) (h1 : 2052 ≤ k) (h2 : k < 2072) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2062 then cr_2052_2062 k h1 h else cr_2062_2072 k (by omega) h2
theorem cr_2072_2073 (k : ℕ) (h1 : 2072 ≤ k) (h2 : k < 2073) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2072 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2072_ok
theorem cr_2073_2074 (k : ℕ) (h1 : 2073 ≤ k) (h2 : k < 2074) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2073 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2073_ok
theorem cr_2072_2074 (k : ℕ) (h1 : 2072 ≤ k) (h2 : k < 2074) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2073 then cr_2072_2073 k h1 h else cr_2073_2074 k (by omega) h2
theorem cr_2074_2075 (k : ℕ) (h1 : 2074 ≤ k) (h2 : k < 2075) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2074 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2074_ok
theorem cr_2075_2076 (k : ℕ) (h1 : 2075 ≤ k) (h2 : k < 2076) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2075 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2075_ok
theorem cr_2076_2077 (k : ℕ) (h1 : 2076 ≤ k) (h2 : k < 2077) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2076 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2076_ok
theorem cr_2075_2077 (k : ℕ) (h1 : 2075 ≤ k) (h2 : k < 2077) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2076 then cr_2075_2076 k h1 h else cr_2076_2077 k (by omega) h2
theorem cr_2074_2077 (k : ℕ) (h1 : 2074 ≤ k) (h2 : k < 2077) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2075 then cr_2074_2075 k h1 h else cr_2075_2077 k (by omega) h2
theorem cr_2072_2077 (k : ℕ) (h1 : 2072 ≤ k) (h2 : k < 2077) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2074 then cr_2072_2074 k h1 h else cr_2074_2077 k (by omega) h2
theorem cr_2077_2078 (k : ℕ) (h1 : 2077 ≤ k) (h2 : k < 2078) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2077 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2077_ok
theorem cr_2078_2079 (k : ℕ) (h1 : 2078 ≤ k) (h2 : k < 2079) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2078 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2078_ok
theorem cr_2077_2079 (k : ℕ) (h1 : 2077 ≤ k) (h2 : k < 2079) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2078 then cr_2077_2078 k h1 h else cr_2078_2079 k (by omega) h2
theorem cr_2079_2080 (k : ℕ) (h1 : 2079 ≤ k) (h2 : k < 2080) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2079 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2079_ok
theorem cr_2080_2081 (k : ℕ) (h1 : 2080 ≤ k) (h2 : k < 2081) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2080 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2080_ok
theorem cr_2081_2082 (k : ℕ) (h1 : 2081 ≤ k) (h2 : k < 2082) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2081 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2081_ok
theorem cr_2080_2082 (k : ℕ) (h1 : 2080 ≤ k) (h2 : k < 2082) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2081 then cr_2080_2081 k h1 h else cr_2081_2082 k (by omega) h2
theorem cr_2079_2082 (k : ℕ) (h1 : 2079 ≤ k) (h2 : k < 2082) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2080 then cr_2079_2080 k h1 h else cr_2080_2082 k (by omega) h2
theorem cr_2077_2082 (k : ℕ) (h1 : 2077 ≤ k) (h2 : k < 2082) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2079 then cr_2077_2079 k h1 h else cr_2079_2082 k (by omega) h2
theorem cr_2072_2082 (k : ℕ) (h1 : 2072 ≤ k) (h2 : k < 2082) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2077 then cr_2072_2077 k h1 h else cr_2077_2082 k (by omega) h2
theorem cr_2082_2083 (k : ℕ) (h1 : 2082 ≤ k) (h2 : k < 2083) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2082 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2082_ok
theorem cr_2083_2084 (k : ℕ) (h1 : 2083 ≤ k) (h2 : k < 2084) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2083 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2083_ok
theorem cr_2082_2084 (k : ℕ) (h1 : 2082 ≤ k) (h2 : k < 2084) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2083 then cr_2082_2083 k h1 h else cr_2083_2084 k (by omega) h2
theorem cr_2084_2085 (k : ℕ) (h1 : 2084 ≤ k) (h2 : k < 2085) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2084 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2084_ok
theorem cr_2085_2086 (k : ℕ) (h1 : 2085 ≤ k) (h2 : k < 2086) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2085 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2085_ok
theorem cr_2086_2087 (k : ℕ) (h1 : 2086 ≤ k) (h2 : k < 2087) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2086 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2086_ok
theorem cr_2085_2087 (k : ℕ) (h1 : 2085 ≤ k) (h2 : k < 2087) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2086 then cr_2085_2086 k h1 h else cr_2086_2087 k (by omega) h2
theorem cr_2084_2087 (k : ℕ) (h1 : 2084 ≤ k) (h2 : k < 2087) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2085 then cr_2084_2085 k h1 h else cr_2085_2087 k (by omega) h2
theorem cr_2082_2087 (k : ℕ) (h1 : 2082 ≤ k) (h2 : k < 2087) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2084 then cr_2082_2084 k h1 h else cr_2084_2087 k (by omega) h2
theorem cr_2087_2088 (k : ℕ) (h1 : 2087 ≤ k) (h2 : k < 2088) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2087 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2087_ok
theorem cr_2088_2089 (k : ℕ) (h1 : 2088 ≤ k) (h2 : k < 2089) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2088 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2088_ok
theorem cr_2089_2090 (k : ℕ) (h1 : 2089 ≤ k) (h2 : k < 2090) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2089 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2089_ok
theorem cr_2088_2090 (k : ℕ) (h1 : 2088 ≤ k) (h2 : k < 2090) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2089 then cr_2088_2089 k h1 h else cr_2089_2090 k (by omega) h2
theorem cr_2087_2090 (k : ℕ) (h1 : 2087 ≤ k) (h2 : k < 2090) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2088 then cr_2087_2088 k h1 h else cr_2088_2090 k (by omega) h2
theorem cr_2090_2091 (k : ℕ) (h1 : 2090 ≤ k) (h2 : k < 2091) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2090 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2090_ok
theorem cr_2091_2092 (k : ℕ) (h1 : 2091 ≤ k) (h2 : k < 2092) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2091 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2091_ok
theorem cr_2092_2093 (k : ℕ) (h1 : 2092 ≤ k) (h2 : k < 2093) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2092 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2092_ok
theorem cr_2091_2093 (k : ℕ) (h1 : 2091 ≤ k) (h2 : k < 2093) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2092 then cr_2091_2092 k h1 h else cr_2092_2093 k (by omega) h2
theorem cr_2090_2093 (k : ℕ) (h1 : 2090 ≤ k) (h2 : k < 2093) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2091 then cr_2090_2091 k h1 h else cr_2091_2093 k (by omega) h2
theorem cr_2087_2093 (k : ℕ) (h1 : 2087 ≤ k) (h2 : k < 2093) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2090 then cr_2087_2090 k h1 h else cr_2090_2093 k (by omega) h2
theorem cr_2082_2093 (k : ℕ) (h1 : 2082 ≤ k) (h2 : k < 2093) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2087 then cr_2082_2087 k h1 h else cr_2087_2093 k (by omega) h2
theorem cr_2072_2093 (k : ℕ) (h1 : 2072 ≤ k) (h2 : k < 2093) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2082 then cr_2072_2082 k h1 h else cr_2082_2093 k (by omega) h2
theorem cr_2052_2093 (k : ℕ) (h1 : 2052 ≤ k) (h2 : k < 2093) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2072 then cr_2052_2072 k h1 h else cr_2072_2093 k (by omega) h2
theorem cr_2093_2094 (k : ℕ) (h1 : 2093 ≤ k) (h2 : k < 2094) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2093 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2093_ok
theorem cr_2094_2095 (k : ℕ) (h1 : 2094 ≤ k) (h2 : k < 2095) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2094 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2094_ok
theorem cr_2093_2095 (k : ℕ) (h1 : 2093 ≤ k) (h2 : k < 2095) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2094 then cr_2093_2094 k h1 h else cr_2094_2095 k (by omega) h2
theorem cr_2095_2096 (k : ℕ) (h1 : 2095 ≤ k) (h2 : k < 2096) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2095 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2095_ok
theorem cr_2096_2097 (k : ℕ) (h1 : 2096 ≤ k) (h2 : k < 2097) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2096 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2096_ok
theorem cr_2097_2098 (k : ℕ) (h1 : 2097 ≤ k) (h2 : k < 2098) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2097 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2097_ok
theorem cr_2096_2098 (k : ℕ) (h1 : 2096 ≤ k) (h2 : k < 2098) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2097 then cr_2096_2097 k h1 h else cr_2097_2098 k (by omega) h2
theorem cr_2095_2098 (k : ℕ) (h1 : 2095 ≤ k) (h2 : k < 2098) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2096 then cr_2095_2096 k h1 h else cr_2096_2098 k (by omega) h2
theorem cr_2093_2098 (k : ℕ) (h1 : 2093 ≤ k) (h2 : k < 2098) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2095 then cr_2093_2095 k h1 h else cr_2095_2098 k (by omega) h2
theorem cr_2098_2099 (k : ℕ) (h1 : 2098 ≤ k) (h2 : k < 2099) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2098 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2098_ok
theorem cr_2099_2100 (k : ℕ) (h1 : 2099 ≤ k) (h2 : k < 2100) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2099 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2099_ok
theorem cr_2098_2100 (k : ℕ) (h1 : 2098 ≤ k) (h2 : k < 2100) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2099 then cr_2098_2099 k h1 h else cr_2099_2100 k (by omega) h2
theorem cr_2100_2101 (k : ℕ) (h1 : 2100 ≤ k) (h2 : k < 2101) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2100 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2100_ok
theorem cr_2101_2102 (k : ℕ) (h1 : 2101 ≤ k) (h2 : k < 2102) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2101 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2101_ok
theorem cr_2102_2103 (k : ℕ) (h1 : 2102 ≤ k) (h2 : k < 2103) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2102 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2102_ok
theorem cr_2101_2103 (k : ℕ) (h1 : 2101 ≤ k) (h2 : k < 2103) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2102 then cr_2101_2102 k h1 h else cr_2102_2103 k (by omega) h2
theorem cr_2100_2103 (k : ℕ) (h1 : 2100 ≤ k) (h2 : k < 2103) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2101 then cr_2100_2101 k h1 h else cr_2101_2103 k (by omega) h2
theorem cr_2098_2103 (k : ℕ) (h1 : 2098 ≤ k) (h2 : k < 2103) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2100 then cr_2098_2100 k h1 h else cr_2100_2103 k (by omega) h2
theorem cr_2093_2103 (k : ℕ) (h1 : 2093 ≤ k) (h2 : k < 2103) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2098 then cr_2093_2098 k h1 h else cr_2098_2103 k (by omega) h2
theorem cr_2103_2104 (k : ℕ) (h1 : 2103 ≤ k) (h2 : k < 2104) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2103 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2103_ok
theorem cr_2104_2105 (k : ℕ) (h1 : 2104 ≤ k) (h2 : k < 2105) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2104 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2104_ok
theorem cr_2103_2105 (k : ℕ) (h1 : 2103 ≤ k) (h2 : k < 2105) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2104 then cr_2103_2104 k h1 h else cr_2104_2105 k (by omega) h2
theorem cr_2105_2106 (k : ℕ) (h1 : 2105 ≤ k) (h2 : k < 2106) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2105 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2105_ok
theorem cr_2106_2107 (k : ℕ) (h1 : 2106 ≤ k) (h2 : k < 2107) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2106 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2106_ok
theorem cr_2107_2108 (k : ℕ) (h1 : 2107 ≤ k) (h2 : k < 2108) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2107 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2107_ok
theorem cr_2106_2108 (k : ℕ) (h1 : 2106 ≤ k) (h2 : k < 2108) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2107 then cr_2106_2107 k h1 h else cr_2107_2108 k (by omega) h2
theorem cr_2105_2108 (k : ℕ) (h1 : 2105 ≤ k) (h2 : k < 2108) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2106 then cr_2105_2106 k h1 h else cr_2106_2108 k (by omega) h2
theorem cr_2103_2108 (k : ℕ) (h1 : 2103 ≤ k) (h2 : k < 2108) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2105 then cr_2103_2105 k h1 h else cr_2105_2108 k (by omega) h2
theorem cr_2108_2109 (k : ℕ) (h1 : 2108 ≤ k) (h2 : k < 2109) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2108 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2108_ok
theorem cr_2109_2110 (k : ℕ) (h1 : 2109 ≤ k) (h2 : k < 2110) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2109 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2109_ok
theorem cr_2108_2110 (k : ℕ) (h1 : 2108 ≤ k) (h2 : k < 2110) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2109 then cr_2108_2109 k h1 h else cr_2109_2110 k (by omega) h2
theorem cr_2110_2111 (k : ℕ) (h1 : 2110 ≤ k) (h2 : k < 2111) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2110 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2110_ok
theorem cr_2111_2112 (k : ℕ) (h1 : 2111 ≤ k) (h2 : k < 2112) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2111 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2111_ok
theorem cr_2112_2113 (k : ℕ) (h1 : 2112 ≤ k) (h2 : k < 2113) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2112 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2112_ok
theorem cr_2111_2113 (k : ℕ) (h1 : 2111 ≤ k) (h2 : k < 2113) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2112 then cr_2111_2112 k h1 h else cr_2112_2113 k (by omega) h2
theorem cr_2110_2113 (k : ℕ) (h1 : 2110 ≤ k) (h2 : k < 2113) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2111 then cr_2110_2111 k h1 h else cr_2111_2113 k (by omega) h2
theorem cr_2108_2113 (k : ℕ) (h1 : 2108 ≤ k) (h2 : k < 2113) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2110 then cr_2108_2110 k h1 h else cr_2110_2113 k (by omega) h2
theorem cr_2103_2113 (k : ℕ) (h1 : 2103 ≤ k) (h2 : k < 2113) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2108 then cr_2103_2108 k h1 h else cr_2108_2113 k (by omega) h2
theorem cr_2093_2113 (k : ℕ) (h1 : 2093 ≤ k) (h2 : k < 2113) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2103 then cr_2093_2103 k h1 h else cr_2103_2113 k (by omega) h2
theorem cr_2113_2114 (k : ℕ) (h1 : 2113 ≤ k) (h2 : k < 2114) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2113 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2113_ok
theorem cr_2114_2115 (k : ℕ) (h1 : 2114 ≤ k) (h2 : k < 2115) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2114 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2114_ok
theorem cr_2113_2115 (k : ℕ) (h1 : 2113 ≤ k) (h2 : k < 2115) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2114 then cr_2113_2114 k h1 h else cr_2114_2115 k (by omega) h2
theorem cr_2115_2116 (k : ℕ) (h1 : 2115 ≤ k) (h2 : k < 2116) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2115 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2115_ok
theorem cr_2116_2117 (k : ℕ) (h1 : 2116 ≤ k) (h2 : k < 2117) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2116 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2116_ok
theorem cr_2117_2118 (k : ℕ) (h1 : 2117 ≤ k) (h2 : k < 2118) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2117 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2117_ok
theorem cr_2116_2118 (k : ℕ) (h1 : 2116 ≤ k) (h2 : k < 2118) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2117 then cr_2116_2117 k h1 h else cr_2117_2118 k (by omega) h2
theorem cr_2115_2118 (k : ℕ) (h1 : 2115 ≤ k) (h2 : k < 2118) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2116 then cr_2115_2116 k h1 h else cr_2116_2118 k (by omega) h2
theorem cr_2113_2118 (k : ℕ) (h1 : 2113 ≤ k) (h2 : k < 2118) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2115 then cr_2113_2115 k h1 h else cr_2115_2118 k (by omega) h2
theorem cr_2118_2119 (k : ℕ) (h1 : 2118 ≤ k) (h2 : k < 2119) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2118 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2118_ok
theorem cr_2119_2120 (k : ℕ) (h1 : 2119 ≤ k) (h2 : k < 2120) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2119 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2119_ok
theorem cr_2118_2120 (k : ℕ) (h1 : 2118 ≤ k) (h2 : k < 2120) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2119 then cr_2118_2119 k h1 h else cr_2119_2120 k (by omega) h2
theorem cr_2120_2121 (k : ℕ) (h1 : 2120 ≤ k) (h2 : k < 2121) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2120 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2120_ok
theorem cr_2121_2122 (k : ℕ) (h1 : 2121 ≤ k) (h2 : k < 2122) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2121 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2121_ok
theorem cr_2122_2123 (k : ℕ) (h1 : 2122 ≤ k) (h2 : k < 2123) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2122 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2122_ok
theorem cr_2121_2123 (k : ℕ) (h1 : 2121 ≤ k) (h2 : k < 2123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2122 then cr_2121_2122 k h1 h else cr_2122_2123 k (by omega) h2
theorem cr_2120_2123 (k : ℕ) (h1 : 2120 ≤ k) (h2 : k < 2123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2121 then cr_2120_2121 k h1 h else cr_2121_2123 k (by omega) h2
theorem cr_2118_2123 (k : ℕ) (h1 : 2118 ≤ k) (h2 : k < 2123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2120 then cr_2118_2120 k h1 h else cr_2120_2123 k (by omega) h2
theorem cr_2113_2123 (k : ℕ) (h1 : 2113 ≤ k) (h2 : k < 2123) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2118 then cr_2113_2118 k h1 h else cr_2118_2123 k (by omega) h2
theorem cr_2123_2124 (k : ℕ) (h1 : 2123 ≤ k) (h2 : k < 2124) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2123 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2123_ok
theorem cr_2124_2125 (k : ℕ) (h1 : 2124 ≤ k) (h2 : k < 2125) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2124 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2124_ok
theorem cr_2123_2125 (k : ℕ) (h1 : 2123 ≤ k) (h2 : k < 2125) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2124 then cr_2123_2124 k h1 h else cr_2124_2125 k (by omega) h2
theorem cr_2125_2126 (k : ℕ) (h1 : 2125 ≤ k) (h2 : k < 2126) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2125 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2125_ok
theorem cr_2126_2127 (k : ℕ) (h1 : 2126 ≤ k) (h2 : k < 2127) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2126 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2126_ok
theorem cr_2127_2128 (k : ℕ) (h1 : 2127 ≤ k) (h2 : k < 2128) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2127 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2127_ok
theorem cr_2126_2128 (k : ℕ) (h1 : 2126 ≤ k) (h2 : k < 2128) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2127 then cr_2126_2127 k h1 h else cr_2127_2128 k (by omega) h2
theorem cr_2125_2128 (k : ℕ) (h1 : 2125 ≤ k) (h2 : k < 2128) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2126 then cr_2125_2126 k h1 h else cr_2126_2128 k (by omega) h2
theorem cr_2123_2128 (k : ℕ) (h1 : 2123 ≤ k) (h2 : k < 2128) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2125 then cr_2123_2125 k h1 h else cr_2125_2128 k (by omega) h2
theorem cr_2128_2129 (k : ℕ) (h1 : 2128 ≤ k) (h2 : k < 2129) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2128 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2128_ok
theorem cr_2129_2130 (k : ℕ) (h1 : 2129 ≤ k) (h2 : k < 2130) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2129 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2129_ok
theorem cr_2130_2131 (k : ℕ) (h1 : 2130 ≤ k) (h2 : k < 2131) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2130 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2130_ok
theorem cr_2129_2131 (k : ℕ) (h1 : 2129 ≤ k) (h2 : k < 2131) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2130 then cr_2129_2130 k h1 h else cr_2130_2131 k (by omega) h2
theorem cr_2128_2131 (k : ℕ) (h1 : 2128 ≤ k) (h2 : k < 2131) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2129 then cr_2128_2129 k h1 h else cr_2129_2131 k (by omega) h2
theorem cr_2131_2132 (k : ℕ) (h1 : 2131 ≤ k) (h2 : k < 2132) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2131 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2131_ok
theorem cr_2132_2133 (k : ℕ) (h1 : 2132 ≤ k) (h2 : k < 2133) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2132 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2132_ok
theorem cr_2133_2134 (k : ℕ) (h1 : 2133 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2133 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2133_ok
theorem cr_2132_2134 (k : ℕ) (h1 : 2132 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2133 then cr_2132_2133 k h1 h else cr_2133_2134 k (by omega) h2
theorem cr_2131_2134 (k : ℕ) (h1 : 2131 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2132 then cr_2131_2132 k h1 h else cr_2132_2134 k (by omega) h2
theorem cr_2128_2134 (k : ℕ) (h1 : 2128 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2131 then cr_2128_2131 k h1 h else cr_2131_2134 k (by omega) h2
theorem cr_2123_2134 (k : ℕ) (h1 : 2123 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2128 then cr_2123_2128 k h1 h else cr_2128_2134 k (by omega) h2
theorem cr_2113_2134 (k : ℕ) (h1 : 2113 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2123 then cr_2113_2123 k h1 h else cr_2123_2134 k (by omega) h2
theorem cr_2093_2134 (k : ℕ) (h1 : 2093 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2113 then cr_2093_2113 k h1 h else cr_2113_2134 k (by omega) h2
theorem cr_2052_2134 (k : ℕ) (h1 : 2052 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2093 then cr_2052_2093 k h1 h else cr_2093_2134 k (by omega) h2
theorem cr_1970_2134 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 2134) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2052 then cr_1970_2052 k h1 h else cr_2052_2134 k (by omega) h2
theorem cr_2134_2135 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2135) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2134 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2134_ok
theorem cr_2135_2136 (k : ℕ) (h1 : 2135 ≤ k) (h2 : k < 2136) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2135 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2135_ok
theorem cr_2134_2136 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2136) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2135 then cr_2134_2135 k h1 h else cr_2135_2136 k (by omega) h2
theorem cr_2136_2137 (k : ℕ) (h1 : 2136 ≤ k) (h2 : k < 2137) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2136 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2136_ok
theorem cr_2137_2138 (k : ℕ) (h1 : 2137 ≤ k) (h2 : k < 2138) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2137 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2137_ok
theorem cr_2138_2139 (k : ℕ) (h1 : 2138 ≤ k) (h2 : k < 2139) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2138 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2138_ok
theorem cr_2137_2139 (k : ℕ) (h1 : 2137 ≤ k) (h2 : k < 2139) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2138 then cr_2137_2138 k h1 h else cr_2138_2139 k (by omega) h2
theorem cr_2136_2139 (k : ℕ) (h1 : 2136 ≤ k) (h2 : k < 2139) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2137 then cr_2136_2137 k h1 h else cr_2137_2139 k (by omega) h2
theorem cr_2134_2139 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2139) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2136 then cr_2134_2136 k h1 h else cr_2136_2139 k (by omega) h2
theorem cr_2139_2140 (k : ℕ) (h1 : 2139 ≤ k) (h2 : k < 2140) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2139 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2139_ok
theorem cr_2140_2141 (k : ℕ) (h1 : 2140 ≤ k) (h2 : k < 2141) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2140 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2140_ok
theorem cr_2139_2141 (k : ℕ) (h1 : 2139 ≤ k) (h2 : k < 2141) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2140 then cr_2139_2140 k h1 h else cr_2140_2141 k (by omega) h2
theorem cr_2141_2142 (k : ℕ) (h1 : 2141 ≤ k) (h2 : k < 2142) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2141 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2141_ok
theorem cr_2142_2143 (k : ℕ) (h1 : 2142 ≤ k) (h2 : k < 2143) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2142 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2142_ok
theorem cr_2143_2144 (k : ℕ) (h1 : 2143 ≤ k) (h2 : k < 2144) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2143 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2143_ok
theorem cr_2142_2144 (k : ℕ) (h1 : 2142 ≤ k) (h2 : k < 2144) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2143 then cr_2142_2143 k h1 h else cr_2143_2144 k (by omega) h2
theorem cr_2141_2144 (k : ℕ) (h1 : 2141 ≤ k) (h2 : k < 2144) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2142 then cr_2141_2142 k h1 h else cr_2142_2144 k (by omega) h2
theorem cr_2139_2144 (k : ℕ) (h1 : 2139 ≤ k) (h2 : k < 2144) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2141 then cr_2139_2141 k h1 h else cr_2141_2144 k (by omega) h2
theorem cr_2134_2144 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2144) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2139 then cr_2134_2139 k h1 h else cr_2139_2144 k (by omega) h2
theorem cr_2144_2145 (k : ℕ) (h1 : 2144 ≤ k) (h2 : k < 2145) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2144 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2144_ok
theorem cr_2145_2146 (k : ℕ) (h1 : 2145 ≤ k) (h2 : k < 2146) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2145 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2145_ok
theorem cr_2144_2146 (k : ℕ) (h1 : 2144 ≤ k) (h2 : k < 2146) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2145 then cr_2144_2145 k h1 h else cr_2145_2146 k (by omega) h2
theorem cr_2146_2147 (k : ℕ) (h1 : 2146 ≤ k) (h2 : k < 2147) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2146 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2146_ok
theorem cr_2147_2148 (k : ℕ) (h1 : 2147 ≤ k) (h2 : k < 2148) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2147 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2147_ok
theorem cr_2148_2149 (k : ℕ) (h1 : 2148 ≤ k) (h2 : k < 2149) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2148 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2148_ok
theorem cr_2147_2149 (k : ℕ) (h1 : 2147 ≤ k) (h2 : k < 2149) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2148 then cr_2147_2148 k h1 h else cr_2148_2149 k (by omega) h2
theorem cr_2146_2149 (k : ℕ) (h1 : 2146 ≤ k) (h2 : k < 2149) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2147 then cr_2146_2147 k h1 h else cr_2147_2149 k (by omega) h2
theorem cr_2144_2149 (k : ℕ) (h1 : 2144 ≤ k) (h2 : k < 2149) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2146 then cr_2144_2146 k h1 h else cr_2146_2149 k (by omega) h2
theorem cr_2149_2150 (k : ℕ) (h1 : 2149 ≤ k) (h2 : k < 2150) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2149 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2149_ok
theorem cr_2150_2151 (k : ℕ) (h1 : 2150 ≤ k) (h2 : k < 2151) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2150 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2150_ok
theorem cr_2149_2151 (k : ℕ) (h1 : 2149 ≤ k) (h2 : k < 2151) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2150 then cr_2149_2150 k h1 h else cr_2150_2151 k (by omega) h2
theorem cr_2151_2152 (k : ℕ) (h1 : 2151 ≤ k) (h2 : k < 2152) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2151 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2151_ok
theorem cr_2152_2153 (k : ℕ) (h1 : 2152 ≤ k) (h2 : k < 2153) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2152 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2152_ok
theorem cr_2153_2154 (k : ℕ) (h1 : 2153 ≤ k) (h2 : k < 2154) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2153 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2153_ok
theorem cr_2152_2154 (k : ℕ) (h1 : 2152 ≤ k) (h2 : k < 2154) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2153 then cr_2152_2153 k h1 h else cr_2153_2154 k (by omega) h2
theorem cr_2151_2154 (k : ℕ) (h1 : 2151 ≤ k) (h2 : k < 2154) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2152 then cr_2151_2152 k h1 h else cr_2152_2154 k (by omega) h2
theorem cr_2149_2154 (k : ℕ) (h1 : 2149 ≤ k) (h2 : k < 2154) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2151 then cr_2149_2151 k h1 h else cr_2151_2154 k (by omega) h2
theorem cr_2144_2154 (k : ℕ) (h1 : 2144 ≤ k) (h2 : k < 2154) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2149 then cr_2144_2149 k h1 h else cr_2149_2154 k (by omega) h2
theorem cr_2134_2154 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2154) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2144 then cr_2134_2144 k h1 h else cr_2144_2154 k (by omega) h2
theorem cr_2154_2155 (k : ℕ) (h1 : 2154 ≤ k) (h2 : k < 2155) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2154 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2154_ok
theorem cr_2155_2156 (k : ℕ) (h1 : 2155 ≤ k) (h2 : k < 2156) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2155 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2155_ok
theorem cr_2154_2156 (k : ℕ) (h1 : 2154 ≤ k) (h2 : k < 2156) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2155 then cr_2154_2155 k h1 h else cr_2155_2156 k (by omega) h2
theorem cr_2156_2157 (k : ℕ) (h1 : 2156 ≤ k) (h2 : k < 2157) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2156 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2156_ok
theorem cr_2157_2158 (k : ℕ) (h1 : 2157 ≤ k) (h2 : k < 2158) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2157 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2157_ok
theorem cr_2158_2159 (k : ℕ) (h1 : 2158 ≤ k) (h2 : k < 2159) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2158 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2158_ok
theorem cr_2157_2159 (k : ℕ) (h1 : 2157 ≤ k) (h2 : k < 2159) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2158 then cr_2157_2158 k h1 h else cr_2158_2159 k (by omega) h2
theorem cr_2156_2159 (k : ℕ) (h1 : 2156 ≤ k) (h2 : k < 2159) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2157 then cr_2156_2157 k h1 h else cr_2157_2159 k (by omega) h2
theorem cr_2154_2159 (k : ℕ) (h1 : 2154 ≤ k) (h2 : k < 2159) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2156 then cr_2154_2156 k h1 h else cr_2156_2159 k (by omega) h2
theorem cr_2159_2160 (k : ℕ) (h1 : 2159 ≤ k) (h2 : k < 2160) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2159 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2159_ok
theorem cr_2160_2161 (k : ℕ) (h1 : 2160 ≤ k) (h2 : k < 2161) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2160 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2160_ok
theorem cr_2159_2161 (k : ℕ) (h1 : 2159 ≤ k) (h2 : k < 2161) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2160 then cr_2159_2160 k h1 h else cr_2160_2161 k (by omega) h2
theorem cr_2161_2162 (k : ℕ) (h1 : 2161 ≤ k) (h2 : k < 2162) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2161 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2161_ok
theorem cr_2162_2163 (k : ℕ) (h1 : 2162 ≤ k) (h2 : k < 2163) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2162 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2162_ok
theorem cr_2163_2164 (k : ℕ) (h1 : 2163 ≤ k) (h2 : k < 2164) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2163 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2163_ok
theorem cr_2162_2164 (k : ℕ) (h1 : 2162 ≤ k) (h2 : k < 2164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2163 then cr_2162_2163 k h1 h else cr_2163_2164 k (by omega) h2
theorem cr_2161_2164 (k : ℕ) (h1 : 2161 ≤ k) (h2 : k < 2164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2162 then cr_2161_2162 k h1 h else cr_2162_2164 k (by omega) h2
theorem cr_2159_2164 (k : ℕ) (h1 : 2159 ≤ k) (h2 : k < 2164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2161 then cr_2159_2161 k h1 h else cr_2161_2164 k (by omega) h2
theorem cr_2154_2164 (k : ℕ) (h1 : 2154 ≤ k) (h2 : k < 2164) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2159 then cr_2154_2159 k h1 h else cr_2159_2164 k (by omega) h2
theorem cr_2164_2165 (k : ℕ) (h1 : 2164 ≤ k) (h2 : k < 2165) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2164 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2164_ok
theorem cr_2165_2166 (k : ℕ) (h1 : 2165 ≤ k) (h2 : k < 2166) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2165 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2165_ok
theorem cr_2164_2166 (k : ℕ) (h1 : 2164 ≤ k) (h2 : k < 2166) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2165 then cr_2164_2165 k h1 h else cr_2165_2166 k (by omega) h2
theorem cr_2166_2167 (k : ℕ) (h1 : 2166 ≤ k) (h2 : k < 2167) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2166 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2166_ok
theorem cr_2167_2168 (k : ℕ) (h1 : 2167 ≤ k) (h2 : k < 2168) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2167 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2167_ok
theorem cr_2168_2169 (k : ℕ) (h1 : 2168 ≤ k) (h2 : k < 2169) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2168 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2168_ok
theorem cr_2167_2169 (k : ℕ) (h1 : 2167 ≤ k) (h2 : k < 2169) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2168 then cr_2167_2168 k h1 h else cr_2168_2169 k (by omega) h2
theorem cr_2166_2169 (k : ℕ) (h1 : 2166 ≤ k) (h2 : k < 2169) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2167 then cr_2166_2167 k h1 h else cr_2167_2169 k (by omega) h2
theorem cr_2164_2169 (k : ℕ) (h1 : 2164 ≤ k) (h2 : k < 2169) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2166 then cr_2164_2166 k h1 h else cr_2166_2169 k (by omega) h2
theorem cr_2169_2170 (k : ℕ) (h1 : 2169 ≤ k) (h2 : k < 2170) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2169 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2169_ok
theorem cr_2170_2171 (k : ℕ) (h1 : 2170 ≤ k) (h2 : k < 2171) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2170 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2170_ok
theorem cr_2171_2172 (k : ℕ) (h1 : 2171 ≤ k) (h2 : k < 2172) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2171 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2171_ok
theorem cr_2170_2172 (k : ℕ) (h1 : 2170 ≤ k) (h2 : k < 2172) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2171 then cr_2170_2171 k h1 h else cr_2171_2172 k (by omega) h2
theorem cr_2169_2172 (k : ℕ) (h1 : 2169 ≤ k) (h2 : k < 2172) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2170 then cr_2169_2170 k h1 h else cr_2170_2172 k (by omega) h2
theorem cr_2172_2173 (k : ℕ) (h1 : 2172 ≤ k) (h2 : k < 2173) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2172 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2172_ok
theorem cr_2173_2174 (k : ℕ) (h1 : 2173 ≤ k) (h2 : k < 2174) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2173 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2173_ok
theorem cr_2174_2175 (k : ℕ) (h1 : 2174 ≤ k) (h2 : k < 2175) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2174 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2174_ok
theorem cr_2173_2175 (k : ℕ) (h1 : 2173 ≤ k) (h2 : k < 2175) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2174 then cr_2173_2174 k h1 h else cr_2174_2175 k (by omega) h2
theorem cr_2172_2175 (k : ℕ) (h1 : 2172 ≤ k) (h2 : k < 2175) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2173 then cr_2172_2173 k h1 h else cr_2173_2175 k (by omega) h2
theorem cr_2169_2175 (k : ℕ) (h1 : 2169 ≤ k) (h2 : k < 2175) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2172 then cr_2169_2172 k h1 h else cr_2172_2175 k (by omega) h2
theorem cr_2164_2175 (k : ℕ) (h1 : 2164 ≤ k) (h2 : k < 2175) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2169 then cr_2164_2169 k h1 h else cr_2169_2175 k (by omega) h2
theorem cr_2154_2175 (k : ℕ) (h1 : 2154 ≤ k) (h2 : k < 2175) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2164 then cr_2154_2164 k h1 h else cr_2164_2175 k (by omega) h2
theorem cr_2134_2175 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2175) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2154 then cr_2134_2154 k h1 h else cr_2154_2175 k (by omega) h2
theorem cr_2175_2176 (k : ℕ) (h1 : 2175 ≤ k) (h2 : k < 2176) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2175 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2175_ok
theorem cr_2176_2177 (k : ℕ) (h1 : 2176 ≤ k) (h2 : k < 2177) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2176 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2176_ok
theorem cr_2175_2177 (k : ℕ) (h1 : 2175 ≤ k) (h2 : k < 2177) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2176 then cr_2175_2176 k h1 h else cr_2176_2177 k (by omega) h2
theorem cr_2177_2178 (k : ℕ) (h1 : 2177 ≤ k) (h2 : k < 2178) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2177 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2177_ok
theorem cr_2178_2179 (k : ℕ) (h1 : 2178 ≤ k) (h2 : k < 2179) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2178 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2178_ok
theorem cr_2179_2180 (k : ℕ) (h1 : 2179 ≤ k) (h2 : k < 2180) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2179 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2179_ok
theorem cr_2178_2180 (k : ℕ) (h1 : 2178 ≤ k) (h2 : k < 2180) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2179 then cr_2178_2179 k h1 h else cr_2179_2180 k (by omega) h2
theorem cr_2177_2180 (k : ℕ) (h1 : 2177 ≤ k) (h2 : k < 2180) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2178 then cr_2177_2178 k h1 h else cr_2178_2180 k (by omega) h2
theorem cr_2175_2180 (k : ℕ) (h1 : 2175 ≤ k) (h2 : k < 2180) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2177 then cr_2175_2177 k h1 h else cr_2177_2180 k (by omega) h2
theorem cr_2180_2181 (k : ℕ) (h1 : 2180 ≤ k) (h2 : k < 2181) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2180 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2180_ok
theorem cr_2181_2182 (k : ℕ) (h1 : 2181 ≤ k) (h2 : k < 2182) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2181 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2181_ok
theorem cr_2180_2182 (k : ℕ) (h1 : 2180 ≤ k) (h2 : k < 2182) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2181 then cr_2180_2181 k h1 h else cr_2181_2182 k (by omega) h2
theorem cr_2182_2183 (k : ℕ) (h1 : 2182 ≤ k) (h2 : k < 2183) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2182 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2182_ok
theorem cr_2183_2184 (k : ℕ) (h1 : 2183 ≤ k) (h2 : k < 2184) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2183 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2183_ok
theorem cr_2184_2185 (k : ℕ) (h1 : 2184 ≤ k) (h2 : k < 2185) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2184 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2184_ok
theorem cr_2183_2185 (k : ℕ) (h1 : 2183 ≤ k) (h2 : k < 2185) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2184 then cr_2183_2184 k h1 h else cr_2184_2185 k (by omega) h2
theorem cr_2182_2185 (k : ℕ) (h1 : 2182 ≤ k) (h2 : k < 2185) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2183 then cr_2182_2183 k h1 h else cr_2183_2185 k (by omega) h2
theorem cr_2180_2185 (k : ℕ) (h1 : 2180 ≤ k) (h2 : k < 2185) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2182 then cr_2180_2182 k h1 h else cr_2182_2185 k (by omega) h2
theorem cr_2175_2185 (k : ℕ) (h1 : 2175 ≤ k) (h2 : k < 2185) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2180 then cr_2175_2180 k h1 h else cr_2180_2185 k (by omega) h2
theorem cr_2185_2186 (k : ℕ) (h1 : 2185 ≤ k) (h2 : k < 2186) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2185 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2185_ok
theorem cr_2186_2187 (k : ℕ) (h1 : 2186 ≤ k) (h2 : k < 2187) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2186 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2186_ok
theorem cr_2185_2187 (k : ℕ) (h1 : 2185 ≤ k) (h2 : k < 2187) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2186 then cr_2185_2186 k h1 h else cr_2186_2187 k (by omega) h2
theorem cr_2187_2188 (k : ℕ) (h1 : 2187 ≤ k) (h2 : k < 2188) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2187 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2187_ok
theorem cr_2188_2189 (k : ℕ) (h1 : 2188 ≤ k) (h2 : k < 2189) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2188 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2188_ok
theorem cr_2189_2190 (k : ℕ) (h1 : 2189 ≤ k) (h2 : k < 2190) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2189 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2189_ok
theorem cr_2188_2190 (k : ℕ) (h1 : 2188 ≤ k) (h2 : k < 2190) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2189 then cr_2188_2189 k h1 h else cr_2189_2190 k (by omega) h2
theorem cr_2187_2190 (k : ℕ) (h1 : 2187 ≤ k) (h2 : k < 2190) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2188 then cr_2187_2188 k h1 h else cr_2188_2190 k (by omega) h2
theorem cr_2185_2190 (k : ℕ) (h1 : 2185 ≤ k) (h2 : k < 2190) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2187 then cr_2185_2187 k h1 h else cr_2187_2190 k (by omega) h2
theorem cr_2190_2191 (k : ℕ) (h1 : 2190 ≤ k) (h2 : k < 2191) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2190 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2190_ok
theorem cr_2191_2192 (k : ℕ) (h1 : 2191 ≤ k) (h2 : k < 2192) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2191 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2191_ok
theorem cr_2190_2192 (k : ℕ) (h1 : 2190 ≤ k) (h2 : k < 2192) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2191 then cr_2190_2191 k h1 h else cr_2191_2192 k (by omega) h2
theorem cr_2192_2193 (k : ℕ) (h1 : 2192 ≤ k) (h2 : k < 2193) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2192 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2192_ok
theorem cr_2193_2194 (k : ℕ) (h1 : 2193 ≤ k) (h2 : k < 2194) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2193 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2193_ok
theorem cr_2194_2195 (k : ℕ) (h1 : 2194 ≤ k) (h2 : k < 2195) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2194 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2194_ok
theorem cr_2193_2195 (k : ℕ) (h1 : 2193 ≤ k) (h2 : k < 2195) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2194 then cr_2193_2194 k h1 h else cr_2194_2195 k (by omega) h2
theorem cr_2192_2195 (k : ℕ) (h1 : 2192 ≤ k) (h2 : k < 2195) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2193 then cr_2192_2193 k h1 h else cr_2193_2195 k (by omega) h2
theorem cr_2190_2195 (k : ℕ) (h1 : 2190 ≤ k) (h2 : k < 2195) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2192 then cr_2190_2192 k h1 h else cr_2192_2195 k (by omega) h2
theorem cr_2185_2195 (k : ℕ) (h1 : 2185 ≤ k) (h2 : k < 2195) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2190 then cr_2185_2190 k h1 h else cr_2190_2195 k (by omega) h2
theorem cr_2175_2195 (k : ℕ) (h1 : 2175 ≤ k) (h2 : k < 2195) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2185 then cr_2175_2185 k h1 h else cr_2185_2195 k (by omega) h2
theorem cr_2195_2196 (k : ℕ) (h1 : 2195 ≤ k) (h2 : k < 2196) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2195 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2195_ok
theorem cr_2196_2197 (k : ℕ) (h1 : 2196 ≤ k) (h2 : k < 2197) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2196 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2196_ok
theorem cr_2195_2197 (k : ℕ) (h1 : 2195 ≤ k) (h2 : k < 2197) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2196 then cr_2195_2196 k h1 h else cr_2196_2197 k (by omega) h2
theorem cr_2197_2198 (k : ℕ) (h1 : 2197 ≤ k) (h2 : k < 2198) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2197 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2197_ok
theorem cr_2198_2199 (k : ℕ) (h1 : 2198 ≤ k) (h2 : k < 2199) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2198 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2198_ok
theorem cr_2199_2200 (k : ℕ) (h1 : 2199 ≤ k) (h2 : k < 2200) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2199 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2199_ok
theorem cr_2198_2200 (k : ℕ) (h1 : 2198 ≤ k) (h2 : k < 2200) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2199 then cr_2198_2199 k h1 h else cr_2199_2200 k (by omega) h2
theorem cr_2197_2200 (k : ℕ) (h1 : 2197 ≤ k) (h2 : k < 2200) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2198 then cr_2197_2198 k h1 h else cr_2198_2200 k (by omega) h2
theorem cr_2195_2200 (k : ℕ) (h1 : 2195 ≤ k) (h2 : k < 2200) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2197 then cr_2195_2197 k h1 h else cr_2197_2200 k (by omega) h2
theorem cr_2200_2201 (k : ℕ) (h1 : 2200 ≤ k) (h2 : k < 2201) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2200 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2200_ok
theorem cr_2201_2202 (k : ℕ) (h1 : 2201 ≤ k) (h2 : k < 2202) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2201 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2201_ok
theorem cr_2200_2202 (k : ℕ) (h1 : 2200 ≤ k) (h2 : k < 2202) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2201 then cr_2200_2201 k h1 h else cr_2201_2202 k (by omega) h2
theorem cr_2202_2203 (k : ℕ) (h1 : 2202 ≤ k) (h2 : k < 2203) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2202 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2202_ok
theorem cr_2203_2204 (k : ℕ) (h1 : 2203 ≤ k) (h2 : k < 2204) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2203 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2203_ok
theorem cr_2204_2205 (k : ℕ) (h1 : 2204 ≤ k) (h2 : k < 2205) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2204 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2204_ok
theorem cr_2203_2205 (k : ℕ) (h1 : 2203 ≤ k) (h2 : k < 2205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2204 then cr_2203_2204 k h1 h else cr_2204_2205 k (by omega) h2
theorem cr_2202_2205 (k : ℕ) (h1 : 2202 ≤ k) (h2 : k < 2205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2203 then cr_2202_2203 k h1 h else cr_2203_2205 k (by omega) h2
theorem cr_2200_2205 (k : ℕ) (h1 : 2200 ≤ k) (h2 : k < 2205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2202 then cr_2200_2202 k h1 h else cr_2202_2205 k (by omega) h2
theorem cr_2195_2205 (k : ℕ) (h1 : 2195 ≤ k) (h2 : k < 2205) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2200 then cr_2195_2200 k h1 h else cr_2200_2205 k (by omega) h2
theorem cr_2205_2206 (k : ℕ) (h1 : 2205 ≤ k) (h2 : k < 2206) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2205 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2205_ok
theorem cr_2206_2207 (k : ℕ) (h1 : 2206 ≤ k) (h2 : k < 2207) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2206 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2206_ok
theorem cr_2205_2207 (k : ℕ) (h1 : 2205 ≤ k) (h2 : k < 2207) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2206 then cr_2205_2206 k h1 h else cr_2206_2207 k (by omega) h2
theorem cr_2207_2208 (k : ℕ) (h1 : 2207 ≤ k) (h2 : k < 2208) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2207 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2207_ok
theorem cr_2208_2209 (k : ℕ) (h1 : 2208 ≤ k) (h2 : k < 2209) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2208 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2208_ok
theorem cr_2209_2210 (k : ℕ) (h1 : 2209 ≤ k) (h2 : k < 2210) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2209 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2209_ok
theorem cr_2208_2210 (k : ℕ) (h1 : 2208 ≤ k) (h2 : k < 2210) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2209 then cr_2208_2209 k h1 h else cr_2209_2210 k (by omega) h2
theorem cr_2207_2210 (k : ℕ) (h1 : 2207 ≤ k) (h2 : k < 2210) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2208 then cr_2207_2208 k h1 h else cr_2208_2210 k (by omega) h2
theorem cr_2205_2210 (k : ℕ) (h1 : 2205 ≤ k) (h2 : k < 2210) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2207 then cr_2205_2207 k h1 h else cr_2207_2210 k (by omega) h2
theorem cr_2210_2211 (k : ℕ) (h1 : 2210 ≤ k) (h2 : k < 2211) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2210 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2210_ok
theorem cr_2211_2212 (k : ℕ) (h1 : 2211 ≤ k) (h2 : k < 2212) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2211 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2211_ok
theorem cr_2212_2213 (k : ℕ) (h1 : 2212 ≤ k) (h2 : k < 2213) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2212 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2212_ok
theorem cr_2211_2213 (k : ℕ) (h1 : 2211 ≤ k) (h2 : k < 2213) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2212 then cr_2211_2212 k h1 h else cr_2212_2213 k (by omega) h2
theorem cr_2210_2213 (k : ℕ) (h1 : 2210 ≤ k) (h2 : k < 2213) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2211 then cr_2210_2211 k h1 h else cr_2211_2213 k (by omega) h2
theorem cr_2213_2214 (k : ℕ) (h1 : 2213 ≤ k) (h2 : k < 2214) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2213 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2213_ok
theorem cr_2214_2215 (k : ℕ) (h1 : 2214 ≤ k) (h2 : k < 2215) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2214 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2214_ok
theorem cr_2215_2216 (k : ℕ) (h1 : 2215 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2215 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2215_ok
theorem cr_2214_2216 (k : ℕ) (h1 : 2214 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2215 then cr_2214_2215 k h1 h else cr_2215_2216 k (by omega) h2
theorem cr_2213_2216 (k : ℕ) (h1 : 2213 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2214 then cr_2213_2214 k h1 h else cr_2214_2216 k (by omega) h2
theorem cr_2210_2216 (k : ℕ) (h1 : 2210 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2213 then cr_2210_2213 k h1 h else cr_2213_2216 k (by omega) h2
theorem cr_2205_2216 (k : ℕ) (h1 : 2205 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2210 then cr_2205_2210 k h1 h else cr_2210_2216 k (by omega) h2
theorem cr_2195_2216 (k : ℕ) (h1 : 2195 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2205 then cr_2195_2205 k h1 h else cr_2205_2216 k (by omega) h2
theorem cr_2175_2216 (k : ℕ) (h1 : 2175 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2195 then cr_2175_2195 k h1 h else cr_2195_2216 k (by omega) h2
theorem cr_2134_2216 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2216) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2175 then cr_2134_2175 k h1 h else cr_2175_2216 k (by omega) h2
theorem cr_2216_2217 (k : ℕ) (h1 : 2216 ≤ k) (h2 : k < 2217) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2216 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2216_ok
theorem cr_2217_2218 (k : ℕ) (h1 : 2217 ≤ k) (h2 : k < 2218) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2217 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2217_ok
theorem cr_2216_2218 (k : ℕ) (h1 : 2216 ≤ k) (h2 : k < 2218) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2217 then cr_2216_2217 k h1 h else cr_2217_2218 k (by omega) h2
theorem cr_2218_2219 (k : ℕ) (h1 : 2218 ≤ k) (h2 : k < 2219) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2218 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2218_ok
theorem cr_2219_2220 (k : ℕ) (h1 : 2219 ≤ k) (h2 : k < 2220) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2219 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2219_ok
theorem cr_2220_2221 (k : ℕ) (h1 : 2220 ≤ k) (h2 : k < 2221) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2220 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2220_ok
theorem cr_2219_2221 (k : ℕ) (h1 : 2219 ≤ k) (h2 : k < 2221) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2220 then cr_2219_2220 k h1 h else cr_2220_2221 k (by omega) h2
theorem cr_2218_2221 (k : ℕ) (h1 : 2218 ≤ k) (h2 : k < 2221) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2219 then cr_2218_2219 k h1 h else cr_2219_2221 k (by omega) h2
theorem cr_2216_2221 (k : ℕ) (h1 : 2216 ≤ k) (h2 : k < 2221) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2218 then cr_2216_2218 k h1 h else cr_2218_2221 k (by omega) h2
theorem cr_2221_2222 (k : ℕ) (h1 : 2221 ≤ k) (h2 : k < 2222) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2221 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2221_ok
theorem cr_2222_2223 (k : ℕ) (h1 : 2222 ≤ k) (h2 : k < 2223) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2222 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2222_ok
theorem cr_2221_2223 (k : ℕ) (h1 : 2221 ≤ k) (h2 : k < 2223) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2222 then cr_2221_2222 k h1 h else cr_2222_2223 k (by omega) h2
theorem cr_2223_2224 (k : ℕ) (h1 : 2223 ≤ k) (h2 : k < 2224) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2223 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2223_ok
theorem cr_2224_2225 (k : ℕ) (h1 : 2224 ≤ k) (h2 : k < 2225) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2224 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2224_ok
theorem cr_2225_2226 (k : ℕ) (h1 : 2225 ≤ k) (h2 : k < 2226) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2225 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2225_ok
theorem cr_2224_2226 (k : ℕ) (h1 : 2224 ≤ k) (h2 : k < 2226) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2225 then cr_2224_2225 k h1 h else cr_2225_2226 k (by omega) h2
theorem cr_2223_2226 (k : ℕ) (h1 : 2223 ≤ k) (h2 : k < 2226) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2224 then cr_2223_2224 k h1 h else cr_2224_2226 k (by omega) h2
theorem cr_2221_2226 (k : ℕ) (h1 : 2221 ≤ k) (h2 : k < 2226) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2223 then cr_2221_2223 k h1 h else cr_2223_2226 k (by omega) h2
theorem cr_2216_2226 (k : ℕ) (h1 : 2216 ≤ k) (h2 : k < 2226) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2221 then cr_2216_2221 k h1 h else cr_2221_2226 k (by omega) h2
theorem cr_2226_2227 (k : ℕ) (h1 : 2226 ≤ k) (h2 : k < 2227) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2226 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2226_ok
theorem cr_2227_2228 (k : ℕ) (h1 : 2227 ≤ k) (h2 : k < 2228) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2227 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2227_ok
theorem cr_2226_2228 (k : ℕ) (h1 : 2226 ≤ k) (h2 : k < 2228) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2227 then cr_2226_2227 k h1 h else cr_2227_2228 k (by omega) h2
theorem cr_2228_2229 (k : ℕ) (h1 : 2228 ≤ k) (h2 : k < 2229) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2228 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2228_ok
theorem cr_2229_2230 (k : ℕ) (h1 : 2229 ≤ k) (h2 : k < 2230) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2229 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2229_ok
theorem cr_2230_2231 (k : ℕ) (h1 : 2230 ≤ k) (h2 : k < 2231) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2230 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2230_ok
theorem cr_2229_2231 (k : ℕ) (h1 : 2229 ≤ k) (h2 : k < 2231) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2230 then cr_2229_2230 k h1 h else cr_2230_2231 k (by omega) h2
theorem cr_2228_2231 (k : ℕ) (h1 : 2228 ≤ k) (h2 : k < 2231) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2229 then cr_2228_2229 k h1 h else cr_2229_2231 k (by omega) h2
theorem cr_2226_2231 (k : ℕ) (h1 : 2226 ≤ k) (h2 : k < 2231) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2228 then cr_2226_2228 k h1 h else cr_2228_2231 k (by omega) h2
theorem cr_2231_2232 (k : ℕ) (h1 : 2231 ≤ k) (h2 : k < 2232) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2231 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2231_ok
theorem cr_2232_2233 (k : ℕ) (h1 : 2232 ≤ k) (h2 : k < 2233) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2232 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2232_ok
theorem cr_2231_2233 (k : ℕ) (h1 : 2231 ≤ k) (h2 : k < 2233) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2232 then cr_2231_2232 k h1 h else cr_2232_2233 k (by omega) h2
theorem cr_2233_2234 (k : ℕ) (h1 : 2233 ≤ k) (h2 : k < 2234) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2233 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2233_ok
theorem cr_2234_2235 (k : ℕ) (h1 : 2234 ≤ k) (h2 : k < 2235) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2234 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2234_ok
theorem cr_2235_2236 (k : ℕ) (h1 : 2235 ≤ k) (h2 : k < 2236) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2235 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2235_ok
theorem cr_2234_2236 (k : ℕ) (h1 : 2234 ≤ k) (h2 : k < 2236) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2235 then cr_2234_2235 k h1 h else cr_2235_2236 k (by omega) h2
theorem cr_2233_2236 (k : ℕ) (h1 : 2233 ≤ k) (h2 : k < 2236) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2234 then cr_2233_2234 k h1 h else cr_2234_2236 k (by omega) h2
theorem cr_2231_2236 (k : ℕ) (h1 : 2231 ≤ k) (h2 : k < 2236) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2233 then cr_2231_2233 k h1 h else cr_2233_2236 k (by omega) h2
theorem cr_2226_2236 (k : ℕ) (h1 : 2226 ≤ k) (h2 : k < 2236) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2231 then cr_2226_2231 k h1 h else cr_2231_2236 k (by omega) h2
theorem cr_2216_2236 (k : ℕ) (h1 : 2216 ≤ k) (h2 : k < 2236) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2226 then cr_2216_2226 k h1 h else cr_2226_2236 k (by omega) h2
theorem cr_2236_2237 (k : ℕ) (h1 : 2236 ≤ k) (h2 : k < 2237) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2236 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2236_ok
theorem cr_2237_2238 (k : ℕ) (h1 : 2237 ≤ k) (h2 : k < 2238) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2237 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2237_ok
theorem cr_2236_2238 (k : ℕ) (h1 : 2236 ≤ k) (h2 : k < 2238) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2237 then cr_2236_2237 k h1 h else cr_2237_2238 k (by omega) h2
theorem cr_2238_2239 (k : ℕ) (h1 : 2238 ≤ k) (h2 : k < 2239) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2238 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2238_ok
theorem cr_2239_2240 (k : ℕ) (h1 : 2239 ≤ k) (h2 : k < 2240) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2239 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2239_ok
theorem cr_2240_2241 (k : ℕ) (h1 : 2240 ≤ k) (h2 : k < 2241) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2240 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2240_ok
theorem cr_2239_2241 (k : ℕ) (h1 : 2239 ≤ k) (h2 : k < 2241) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2240 then cr_2239_2240 k h1 h else cr_2240_2241 k (by omega) h2
theorem cr_2238_2241 (k : ℕ) (h1 : 2238 ≤ k) (h2 : k < 2241) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2239 then cr_2238_2239 k h1 h else cr_2239_2241 k (by omega) h2
theorem cr_2236_2241 (k : ℕ) (h1 : 2236 ≤ k) (h2 : k < 2241) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2238 then cr_2236_2238 k h1 h else cr_2238_2241 k (by omega) h2
theorem cr_2241_2242 (k : ℕ) (h1 : 2241 ≤ k) (h2 : k < 2242) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2241 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2241_ok
theorem cr_2242_2243 (k : ℕ) (h1 : 2242 ≤ k) (h2 : k < 2243) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2242 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2242_ok
theorem cr_2241_2243 (k : ℕ) (h1 : 2241 ≤ k) (h2 : k < 2243) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2242 then cr_2241_2242 k h1 h else cr_2242_2243 k (by omega) h2
theorem cr_2243_2244 (k : ℕ) (h1 : 2243 ≤ k) (h2 : k < 2244) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2243 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2243_ok
theorem cr_2244_2245 (k : ℕ) (h1 : 2244 ≤ k) (h2 : k < 2245) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2244 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2244_ok
theorem cr_2245_2246 (k : ℕ) (h1 : 2245 ≤ k) (h2 : k < 2246) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2245 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2245_ok
theorem cr_2244_2246 (k : ℕ) (h1 : 2244 ≤ k) (h2 : k < 2246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2245 then cr_2244_2245 k h1 h else cr_2245_2246 k (by omega) h2
theorem cr_2243_2246 (k : ℕ) (h1 : 2243 ≤ k) (h2 : k < 2246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2244 then cr_2243_2244 k h1 h else cr_2244_2246 k (by omega) h2
theorem cr_2241_2246 (k : ℕ) (h1 : 2241 ≤ k) (h2 : k < 2246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2243 then cr_2241_2243 k h1 h else cr_2243_2246 k (by omega) h2
theorem cr_2236_2246 (k : ℕ) (h1 : 2236 ≤ k) (h2 : k < 2246) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2241 then cr_2236_2241 k h1 h else cr_2241_2246 k (by omega) h2
theorem cr_2246_2247 (k : ℕ) (h1 : 2246 ≤ k) (h2 : k < 2247) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2246 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2246_ok
theorem cr_2247_2248 (k : ℕ) (h1 : 2247 ≤ k) (h2 : k < 2248) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2247 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2247_ok
theorem cr_2246_2248 (k : ℕ) (h1 : 2246 ≤ k) (h2 : k < 2248) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2247 then cr_2246_2247 k h1 h else cr_2247_2248 k (by omega) h2
theorem cr_2248_2249 (k : ℕ) (h1 : 2248 ≤ k) (h2 : k < 2249) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2248 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2248_ok
theorem cr_2249_2250 (k : ℕ) (h1 : 2249 ≤ k) (h2 : k < 2250) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2249 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2249_ok
theorem cr_2250_2251 (k : ℕ) (h1 : 2250 ≤ k) (h2 : k < 2251) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2250 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2250_ok
theorem cr_2249_2251 (k : ℕ) (h1 : 2249 ≤ k) (h2 : k < 2251) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2250 then cr_2249_2250 k h1 h else cr_2250_2251 k (by omega) h2
theorem cr_2248_2251 (k : ℕ) (h1 : 2248 ≤ k) (h2 : k < 2251) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2249 then cr_2248_2249 k h1 h else cr_2249_2251 k (by omega) h2
theorem cr_2246_2251 (k : ℕ) (h1 : 2246 ≤ k) (h2 : k < 2251) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2248 then cr_2246_2248 k h1 h else cr_2248_2251 k (by omega) h2
theorem cr_2251_2252 (k : ℕ) (h1 : 2251 ≤ k) (h2 : k < 2252) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2251 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2251_ok
theorem cr_2252_2253 (k : ℕ) (h1 : 2252 ≤ k) (h2 : k < 2253) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2252 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2252_ok
theorem cr_2253_2254 (k : ℕ) (h1 : 2253 ≤ k) (h2 : k < 2254) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2253 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2253_ok
theorem cr_2252_2254 (k : ℕ) (h1 : 2252 ≤ k) (h2 : k < 2254) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2253 then cr_2252_2253 k h1 h else cr_2253_2254 k (by omega) h2
theorem cr_2251_2254 (k : ℕ) (h1 : 2251 ≤ k) (h2 : k < 2254) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2252 then cr_2251_2252 k h1 h else cr_2252_2254 k (by omega) h2
theorem cr_2254_2255 (k : ℕ) (h1 : 2254 ≤ k) (h2 : k < 2255) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2254 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2254_ok
theorem cr_2255_2256 (k : ℕ) (h1 : 2255 ≤ k) (h2 : k < 2256) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2255 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2255_ok
theorem cr_2256_2257 (k : ℕ) (h1 : 2256 ≤ k) (h2 : k < 2257) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2256 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2256_ok
theorem cr_2255_2257 (k : ℕ) (h1 : 2255 ≤ k) (h2 : k < 2257) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2256 then cr_2255_2256 k h1 h else cr_2256_2257 k (by omega) h2
theorem cr_2254_2257 (k : ℕ) (h1 : 2254 ≤ k) (h2 : k < 2257) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2255 then cr_2254_2255 k h1 h else cr_2255_2257 k (by omega) h2
theorem cr_2251_2257 (k : ℕ) (h1 : 2251 ≤ k) (h2 : k < 2257) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2254 then cr_2251_2254 k h1 h else cr_2254_2257 k (by omega) h2
theorem cr_2246_2257 (k : ℕ) (h1 : 2246 ≤ k) (h2 : k < 2257) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2251 then cr_2246_2251 k h1 h else cr_2251_2257 k (by omega) h2
theorem cr_2236_2257 (k : ℕ) (h1 : 2236 ≤ k) (h2 : k < 2257) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2246 then cr_2236_2246 k h1 h else cr_2246_2257 k (by omega) h2
theorem cr_2216_2257 (k : ℕ) (h1 : 2216 ≤ k) (h2 : k < 2257) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2236 then cr_2216_2236 k h1 h else cr_2236_2257 k (by omega) h2
theorem cr_2257_2258 (k : ℕ) (h1 : 2257 ≤ k) (h2 : k < 2258) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2257 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2257_ok
theorem cr_2258_2259 (k : ℕ) (h1 : 2258 ≤ k) (h2 : k < 2259) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2258 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2258_ok
theorem cr_2257_2259 (k : ℕ) (h1 : 2257 ≤ k) (h2 : k < 2259) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2258 then cr_2257_2258 k h1 h else cr_2258_2259 k (by omega) h2
theorem cr_2259_2260 (k : ℕ) (h1 : 2259 ≤ k) (h2 : k < 2260) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2259 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2259_ok
theorem cr_2260_2261 (k : ℕ) (h1 : 2260 ≤ k) (h2 : k < 2261) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2260 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2260_ok
theorem cr_2261_2262 (k : ℕ) (h1 : 2261 ≤ k) (h2 : k < 2262) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2261 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2261_ok
theorem cr_2260_2262 (k : ℕ) (h1 : 2260 ≤ k) (h2 : k < 2262) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2261 then cr_2260_2261 k h1 h else cr_2261_2262 k (by omega) h2
theorem cr_2259_2262 (k : ℕ) (h1 : 2259 ≤ k) (h2 : k < 2262) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2260 then cr_2259_2260 k h1 h else cr_2260_2262 k (by omega) h2
theorem cr_2257_2262 (k : ℕ) (h1 : 2257 ≤ k) (h2 : k < 2262) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2259 then cr_2257_2259 k h1 h else cr_2259_2262 k (by omega) h2
theorem cr_2262_2263 (k : ℕ) (h1 : 2262 ≤ k) (h2 : k < 2263) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2262 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2262_ok
theorem cr_2263_2264 (k : ℕ) (h1 : 2263 ≤ k) (h2 : k < 2264) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2263 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2263_ok
theorem cr_2262_2264 (k : ℕ) (h1 : 2262 ≤ k) (h2 : k < 2264) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2263 then cr_2262_2263 k h1 h else cr_2263_2264 k (by omega) h2
theorem cr_2264_2265 (k : ℕ) (h1 : 2264 ≤ k) (h2 : k < 2265) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2264 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2264_ok
theorem cr_2265_2266 (k : ℕ) (h1 : 2265 ≤ k) (h2 : k < 2266) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2265 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2265_ok
theorem cr_2266_2267 (k : ℕ) (h1 : 2266 ≤ k) (h2 : k < 2267) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2266 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2266_ok
theorem cr_2265_2267 (k : ℕ) (h1 : 2265 ≤ k) (h2 : k < 2267) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2266 then cr_2265_2266 k h1 h else cr_2266_2267 k (by omega) h2
theorem cr_2264_2267 (k : ℕ) (h1 : 2264 ≤ k) (h2 : k < 2267) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2265 then cr_2264_2265 k h1 h else cr_2265_2267 k (by omega) h2
theorem cr_2262_2267 (k : ℕ) (h1 : 2262 ≤ k) (h2 : k < 2267) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2264 then cr_2262_2264 k h1 h else cr_2264_2267 k (by omega) h2
theorem cr_2257_2267 (k : ℕ) (h1 : 2257 ≤ k) (h2 : k < 2267) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2262 then cr_2257_2262 k h1 h else cr_2262_2267 k (by omega) h2
theorem cr_2267_2268 (k : ℕ) (h1 : 2267 ≤ k) (h2 : k < 2268) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2267 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2267_ok
theorem cr_2268_2269 (k : ℕ) (h1 : 2268 ≤ k) (h2 : k < 2269) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2268 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2268_ok
theorem cr_2267_2269 (k : ℕ) (h1 : 2267 ≤ k) (h2 : k < 2269) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2268 then cr_2267_2268 k h1 h else cr_2268_2269 k (by omega) h2
theorem cr_2269_2270 (k : ℕ) (h1 : 2269 ≤ k) (h2 : k < 2270) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2269 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2269_ok
theorem cr_2270_2271 (k : ℕ) (h1 : 2270 ≤ k) (h2 : k < 2271) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2270 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2270_ok
theorem cr_2271_2272 (k : ℕ) (h1 : 2271 ≤ k) (h2 : k < 2272) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2271 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2271_ok
theorem cr_2270_2272 (k : ℕ) (h1 : 2270 ≤ k) (h2 : k < 2272) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2271 then cr_2270_2271 k h1 h else cr_2271_2272 k (by omega) h2
theorem cr_2269_2272 (k : ℕ) (h1 : 2269 ≤ k) (h2 : k < 2272) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2270 then cr_2269_2270 k h1 h else cr_2270_2272 k (by omega) h2
theorem cr_2267_2272 (k : ℕ) (h1 : 2267 ≤ k) (h2 : k < 2272) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2269 then cr_2267_2269 k h1 h else cr_2269_2272 k (by omega) h2
theorem cr_2272_2273 (k : ℕ) (h1 : 2272 ≤ k) (h2 : k < 2273) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2272 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2272_ok
theorem cr_2273_2274 (k : ℕ) (h1 : 2273 ≤ k) (h2 : k < 2274) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2273 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2273_ok
theorem cr_2272_2274 (k : ℕ) (h1 : 2272 ≤ k) (h2 : k < 2274) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2273 then cr_2272_2273 k h1 h else cr_2273_2274 k (by omega) h2
theorem cr_2274_2275 (k : ℕ) (h1 : 2274 ≤ k) (h2 : k < 2275) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2274 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2274_ok
theorem cr_2275_2276 (k : ℕ) (h1 : 2275 ≤ k) (h2 : k < 2276) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2275 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2275_ok
theorem cr_2276_2277 (k : ℕ) (h1 : 2276 ≤ k) (h2 : k < 2277) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2276 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2276_ok
theorem cr_2275_2277 (k : ℕ) (h1 : 2275 ≤ k) (h2 : k < 2277) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2276 then cr_2275_2276 k h1 h else cr_2276_2277 k (by omega) h2
theorem cr_2274_2277 (k : ℕ) (h1 : 2274 ≤ k) (h2 : k < 2277) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2275 then cr_2274_2275 k h1 h else cr_2275_2277 k (by omega) h2
theorem cr_2272_2277 (k : ℕ) (h1 : 2272 ≤ k) (h2 : k < 2277) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2274 then cr_2272_2274 k h1 h else cr_2274_2277 k (by omega) h2
theorem cr_2267_2277 (k : ℕ) (h1 : 2267 ≤ k) (h2 : k < 2277) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2272 then cr_2267_2272 k h1 h else cr_2272_2277 k (by omega) h2
theorem cr_2257_2277 (k : ℕ) (h1 : 2257 ≤ k) (h2 : k < 2277) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2267 then cr_2257_2267 k h1 h else cr_2267_2277 k (by omega) h2
theorem cr_2277_2278 (k : ℕ) (h1 : 2277 ≤ k) (h2 : k < 2278) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2277 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2277_ok
theorem cr_2278_2279 (k : ℕ) (h1 : 2278 ≤ k) (h2 : k < 2279) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2278 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2278_ok
theorem cr_2277_2279 (k : ℕ) (h1 : 2277 ≤ k) (h2 : k < 2279) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2278 then cr_2277_2278 k h1 h else cr_2278_2279 k (by omega) h2
theorem cr_2279_2280 (k : ℕ) (h1 : 2279 ≤ k) (h2 : k < 2280) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2279 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2279_ok
theorem cr_2280_2281 (k : ℕ) (h1 : 2280 ≤ k) (h2 : k < 2281) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2280 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2280_ok
theorem cr_2281_2282 (k : ℕ) (h1 : 2281 ≤ k) (h2 : k < 2282) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2281 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2281_ok
theorem cr_2280_2282 (k : ℕ) (h1 : 2280 ≤ k) (h2 : k < 2282) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2281 then cr_2280_2281 k h1 h else cr_2281_2282 k (by omega) h2
theorem cr_2279_2282 (k : ℕ) (h1 : 2279 ≤ k) (h2 : k < 2282) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2280 then cr_2279_2280 k h1 h else cr_2280_2282 k (by omega) h2
theorem cr_2277_2282 (k : ℕ) (h1 : 2277 ≤ k) (h2 : k < 2282) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2279 then cr_2277_2279 k h1 h else cr_2279_2282 k (by omega) h2
theorem cr_2282_2283 (k : ℕ) (h1 : 2282 ≤ k) (h2 : k < 2283) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2282 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2282_ok
theorem cr_2283_2284 (k : ℕ) (h1 : 2283 ≤ k) (h2 : k < 2284) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2283 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2283_ok
theorem cr_2282_2284 (k : ℕ) (h1 : 2282 ≤ k) (h2 : k < 2284) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2283 then cr_2282_2283 k h1 h else cr_2283_2284 k (by omega) h2
theorem cr_2284_2285 (k : ℕ) (h1 : 2284 ≤ k) (h2 : k < 2285) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2284 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2284_ok
theorem cr_2285_2286 (k : ℕ) (h1 : 2285 ≤ k) (h2 : k < 2286) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2285 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2285_ok
theorem cr_2286_2287 (k : ℕ) (h1 : 2286 ≤ k) (h2 : k < 2287) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2286 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2286_ok
theorem cr_2285_2287 (k : ℕ) (h1 : 2285 ≤ k) (h2 : k < 2287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2286 then cr_2285_2286 k h1 h else cr_2286_2287 k (by omega) h2
theorem cr_2284_2287 (k : ℕ) (h1 : 2284 ≤ k) (h2 : k < 2287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2285 then cr_2284_2285 k h1 h else cr_2285_2287 k (by omega) h2
theorem cr_2282_2287 (k : ℕ) (h1 : 2282 ≤ k) (h2 : k < 2287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2284 then cr_2282_2284 k h1 h else cr_2284_2287 k (by omega) h2
theorem cr_2277_2287 (k : ℕ) (h1 : 2277 ≤ k) (h2 : k < 2287) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2282 then cr_2277_2282 k h1 h else cr_2282_2287 k (by omega) h2
theorem cr_2287_2288 (k : ℕ) (h1 : 2287 ≤ k) (h2 : k < 2288) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2287 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2287_ok
theorem cr_2288_2289 (k : ℕ) (h1 : 2288 ≤ k) (h2 : k < 2289) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2288 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2288_ok
theorem cr_2287_2289 (k : ℕ) (h1 : 2287 ≤ k) (h2 : k < 2289) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2288 then cr_2287_2288 k h1 h else cr_2288_2289 k (by omega) h2
theorem cr_2289_2290 (k : ℕ) (h1 : 2289 ≤ k) (h2 : k < 2290) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2289 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2289_ok
theorem cr_2290_2291 (k : ℕ) (h1 : 2290 ≤ k) (h2 : k < 2291) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2290 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2290_ok
theorem cr_2291_2292 (k : ℕ) (h1 : 2291 ≤ k) (h2 : k < 2292) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2291 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2291_ok
theorem cr_2290_2292 (k : ℕ) (h1 : 2290 ≤ k) (h2 : k < 2292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2291 then cr_2290_2291 k h1 h else cr_2291_2292 k (by omega) h2
theorem cr_2289_2292 (k : ℕ) (h1 : 2289 ≤ k) (h2 : k < 2292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2290 then cr_2289_2290 k h1 h else cr_2290_2292 k (by omega) h2
theorem cr_2287_2292 (k : ℕ) (h1 : 2287 ≤ k) (h2 : k < 2292) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2289 then cr_2287_2289 k h1 h else cr_2289_2292 k (by omega) h2
theorem cr_2292_2293 (k : ℕ) (h1 : 2292 ≤ k) (h2 : k < 2293) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2292 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2292_ok
theorem cr_2293_2294 (k : ℕ) (h1 : 2293 ≤ k) (h2 : k < 2294) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2293 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2293_ok
theorem cr_2294_2295 (k : ℕ) (h1 : 2294 ≤ k) (h2 : k < 2295) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2294 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2294_ok
theorem cr_2293_2295 (k : ℕ) (h1 : 2293 ≤ k) (h2 : k < 2295) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2294 then cr_2293_2294 k h1 h else cr_2294_2295 k (by omega) h2
theorem cr_2292_2295 (k : ℕ) (h1 : 2292 ≤ k) (h2 : k < 2295) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2293 then cr_2292_2293 k h1 h else cr_2293_2295 k (by omega) h2
theorem cr_2295_2296 (k : ℕ) (h1 : 2295 ≤ k) (h2 : k < 2296) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2295 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2295_ok
theorem cr_2296_2297 (k : ℕ) (h1 : 2296 ≤ k) (h2 : k < 2297) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2296 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2296_ok
theorem cr_2297_2298 (k : ℕ) (h1 : 2297 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2297 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2297_ok
theorem cr_2296_2298 (k : ℕ) (h1 : 2296 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2297 then cr_2296_2297 k h1 h else cr_2297_2298 k (by omega) h2
theorem cr_2295_2298 (k : ℕ) (h1 : 2295 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2296 then cr_2295_2296 k h1 h else cr_2296_2298 k (by omega) h2
theorem cr_2292_2298 (k : ℕ) (h1 : 2292 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2295 then cr_2292_2295 k h1 h else cr_2295_2298 k (by omega) h2
theorem cr_2287_2298 (k : ℕ) (h1 : 2287 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2292 then cr_2287_2292 k h1 h else cr_2292_2298 k (by omega) h2
theorem cr_2277_2298 (k : ℕ) (h1 : 2277 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2287 then cr_2277_2287 k h1 h else cr_2287_2298 k (by omega) h2
theorem cr_2257_2298 (k : ℕ) (h1 : 2257 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2277 then cr_2257_2277 k h1 h else cr_2277_2298 k (by omega) h2
theorem cr_2216_2298 (k : ℕ) (h1 : 2216 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2257 then cr_2216_2257 k h1 h else cr_2257_2298 k (by omega) h2
theorem cr_2134_2298 (k : ℕ) (h1 : 2134 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2216 then cr_2134_2216 k h1 h else cr_2216_2298 k (by omega) h2
theorem cr_1970_2298 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 2298) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2134 then cr_1970_2134 k h1 h else cr_2134_2298 k (by omega) h2
theorem cr_2298_2299 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2299) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2298 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2298_ok
theorem cr_2299_2300 (k : ℕ) (h1 : 2299 ≤ k) (h2 : k < 2300) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2299 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2299_ok
theorem cr_2298_2300 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2300) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2299 then cr_2298_2299 k h1 h else cr_2299_2300 k (by omega) h2
theorem cr_2300_2301 (k : ℕ) (h1 : 2300 ≤ k) (h2 : k < 2301) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2300 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2300_ok
theorem cr_2301_2302 (k : ℕ) (h1 : 2301 ≤ k) (h2 : k < 2302) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2301 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2301_ok
theorem cr_2302_2303 (k : ℕ) (h1 : 2302 ≤ k) (h2 : k < 2303) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2302 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2302_ok
theorem cr_2301_2303 (k : ℕ) (h1 : 2301 ≤ k) (h2 : k < 2303) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2302 then cr_2301_2302 k h1 h else cr_2302_2303 k (by omega) h2
theorem cr_2300_2303 (k : ℕ) (h1 : 2300 ≤ k) (h2 : k < 2303) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2301 then cr_2300_2301 k h1 h else cr_2301_2303 k (by omega) h2
theorem cr_2298_2303 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2303) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2300 then cr_2298_2300 k h1 h else cr_2300_2303 k (by omega) h2
theorem cr_2303_2304 (k : ℕ) (h1 : 2303 ≤ k) (h2 : k < 2304) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2303 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2303_ok
theorem cr_2304_2305 (k : ℕ) (h1 : 2304 ≤ k) (h2 : k < 2305) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2304 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2304_ok
theorem cr_2303_2305 (k : ℕ) (h1 : 2303 ≤ k) (h2 : k < 2305) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2304 then cr_2303_2304 k h1 h else cr_2304_2305 k (by omega) h2
theorem cr_2305_2306 (k : ℕ) (h1 : 2305 ≤ k) (h2 : k < 2306) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2305 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2305_ok
theorem cr_2306_2307 (k : ℕ) (h1 : 2306 ≤ k) (h2 : k < 2307) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2306 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2306_ok
theorem cr_2307_2308 (k : ℕ) (h1 : 2307 ≤ k) (h2 : k < 2308) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2307 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2307_ok
theorem cr_2306_2308 (k : ℕ) (h1 : 2306 ≤ k) (h2 : k < 2308) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2307 then cr_2306_2307 k h1 h else cr_2307_2308 k (by omega) h2
theorem cr_2305_2308 (k : ℕ) (h1 : 2305 ≤ k) (h2 : k < 2308) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2306 then cr_2305_2306 k h1 h else cr_2306_2308 k (by omega) h2
theorem cr_2303_2308 (k : ℕ) (h1 : 2303 ≤ k) (h2 : k < 2308) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2305 then cr_2303_2305 k h1 h else cr_2305_2308 k (by omega) h2
theorem cr_2298_2308 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2308) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2303 then cr_2298_2303 k h1 h else cr_2303_2308 k (by omega) h2
theorem cr_2308_2309 (k : ℕ) (h1 : 2308 ≤ k) (h2 : k < 2309) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2308 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2308_ok
theorem cr_2309_2310 (k : ℕ) (h1 : 2309 ≤ k) (h2 : k < 2310) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2309 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2309_ok
theorem cr_2308_2310 (k : ℕ) (h1 : 2308 ≤ k) (h2 : k < 2310) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2309 then cr_2308_2309 k h1 h else cr_2309_2310 k (by omega) h2
theorem cr_2310_2311 (k : ℕ) (h1 : 2310 ≤ k) (h2 : k < 2311) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2310 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2310_ok
theorem cr_2311_2312 (k : ℕ) (h1 : 2311 ≤ k) (h2 : k < 2312) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2311 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2311_ok
theorem cr_2312_2313 (k : ℕ) (h1 : 2312 ≤ k) (h2 : k < 2313) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2312 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2312_ok
theorem cr_2311_2313 (k : ℕ) (h1 : 2311 ≤ k) (h2 : k < 2313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2312 then cr_2311_2312 k h1 h else cr_2312_2313 k (by omega) h2
theorem cr_2310_2313 (k : ℕ) (h1 : 2310 ≤ k) (h2 : k < 2313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2311 then cr_2310_2311 k h1 h else cr_2311_2313 k (by omega) h2
theorem cr_2308_2313 (k : ℕ) (h1 : 2308 ≤ k) (h2 : k < 2313) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2310 then cr_2308_2310 k h1 h else cr_2310_2313 k (by omega) h2
theorem cr_2313_2314 (k : ℕ) (h1 : 2313 ≤ k) (h2 : k < 2314) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2313 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2313_ok
theorem cr_2314_2315 (k : ℕ) (h1 : 2314 ≤ k) (h2 : k < 2315) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2314 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2314_ok
theorem cr_2313_2315 (k : ℕ) (h1 : 2313 ≤ k) (h2 : k < 2315) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2314 then cr_2313_2314 k h1 h else cr_2314_2315 k (by omega) h2
theorem cr_2315_2316 (k : ℕ) (h1 : 2315 ≤ k) (h2 : k < 2316) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2315 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2315_ok
theorem cr_2316_2317 (k : ℕ) (h1 : 2316 ≤ k) (h2 : k < 2317) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2316 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2316_ok
theorem cr_2317_2318 (k : ℕ) (h1 : 2317 ≤ k) (h2 : k < 2318) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2317 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2317_ok
theorem cr_2316_2318 (k : ℕ) (h1 : 2316 ≤ k) (h2 : k < 2318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2317 then cr_2316_2317 k h1 h else cr_2317_2318 k (by omega) h2
theorem cr_2315_2318 (k : ℕ) (h1 : 2315 ≤ k) (h2 : k < 2318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2316 then cr_2315_2316 k h1 h else cr_2316_2318 k (by omega) h2
theorem cr_2313_2318 (k : ℕ) (h1 : 2313 ≤ k) (h2 : k < 2318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2315 then cr_2313_2315 k h1 h else cr_2315_2318 k (by omega) h2
theorem cr_2308_2318 (k : ℕ) (h1 : 2308 ≤ k) (h2 : k < 2318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2313 then cr_2308_2313 k h1 h else cr_2313_2318 k (by omega) h2
theorem cr_2298_2318 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2318) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2308 then cr_2298_2308 k h1 h else cr_2308_2318 k (by omega) h2
theorem cr_2318_2319 (k : ℕ) (h1 : 2318 ≤ k) (h2 : k < 2319) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2318 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2318_ok
theorem cr_2319_2320 (k : ℕ) (h1 : 2319 ≤ k) (h2 : k < 2320) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2319 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2319_ok
theorem cr_2318_2320 (k : ℕ) (h1 : 2318 ≤ k) (h2 : k < 2320) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2319 then cr_2318_2319 k h1 h else cr_2319_2320 k (by omega) h2
theorem cr_2320_2321 (k : ℕ) (h1 : 2320 ≤ k) (h2 : k < 2321) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2320 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2320_ok
theorem cr_2321_2322 (k : ℕ) (h1 : 2321 ≤ k) (h2 : k < 2322) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2321 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2321_ok
theorem cr_2322_2323 (k : ℕ) (h1 : 2322 ≤ k) (h2 : k < 2323) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2322 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2322_ok
theorem cr_2321_2323 (k : ℕ) (h1 : 2321 ≤ k) (h2 : k < 2323) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2322 then cr_2321_2322 k h1 h else cr_2322_2323 k (by omega) h2
theorem cr_2320_2323 (k : ℕ) (h1 : 2320 ≤ k) (h2 : k < 2323) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2321 then cr_2320_2321 k h1 h else cr_2321_2323 k (by omega) h2
theorem cr_2318_2323 (k : ℕ) (h1 : 2318 ≤ k) (h2 : k < 2323) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2320 then cr_2318_2320 k h1 h else cr_2320_2323 k (by omega) h2
theorem cr_2323_2324 (k : ℕ) (h1 : 2323 ≤ k) (h2 : k < 2324) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2323 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2323_ok
theorem cr_2324_2325 (k : ℕ) (h1 : 2324 ≤ k) (h2 : k < 2325) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2324 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2324_ok
theorem cr_2323_2325 (k : ℕ) (h1 : 2323 ≤ k) (h2 : k < 2325) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2324 then cr_2323_2324 k h1 h else cr_2324_2325 k (by omega) h2
theorem cr_2325_2326 (k : ℕ) (h1 : 2325 ≤ k) (h2 : k < 2326) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2325 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2325_ok
theorem cr_2326_2327 (k : ℕ) (h1 : 2326 ≤ k) (h2 : k < 2327) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2326 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2326_ok
theorem cr_2327_2328 (k : ℕ) (h1 : 2327 ≤ k) (h2 : k < 2328) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2327 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2327_ok
theorem cr_2326_2328 (k : ℕ) (h1 : 2326 ≤ k) (h2 : k < 2328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2327 then cr_2326_2327 k h1 h else cr_2327_2328 k (by omega) h2
theorem cr_2325_2328 (k : ℕ) (h1 : 2325 ≤ k) (h2 : k < 2328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2326 then cr_2325_2326 k h1 h else cr_2326_2328 k (by omega) h2
theorem cr_2323_2328 (k : ℕ) (h1 : 2323 ≤ k) (h2 : k < 2328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2325 then cr_2323_2325 k h1 h else cr_2325_2328 k (by omega) h2
theorem cr_2318_2328 (k : ℕ) (h1 : 2318 ≤ k) (h2 : k < 2328) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2323 then cr_2318_2323 k h1 h else cr_2323_2328 k (by omega) h2
theorem cr_2328_2329 (k : ℕ) (h1 : 2328 ≤ k) (h2 : k < 2329) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2328 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2328_ok
theorem cr_2329_2330 (k : ℕ) (h1 : 2329 ≤ k) (h2 : k < 2330) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2329 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2329_ok
theorem cr_2328_2330 (k : ℕ) (h1 : 2328 ≤ k) (h2 : k < 2330) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2329 then cr_2328_2329 k h1 h else cr_2329_2330 k (by omega) h2
theorem cr_2330_2331 (k : ℕ) (h1 : 2330 ≤ k) (h2 : k < 2331) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2330 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2330_ok
theorem cr_2331_2332 (k : ℕ) (h1 : 2331 ≤ k) (h2 : k < 2332) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2331 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2331_ok
theorem cr_2332_2333 (k : ℕ) (h1 : 2332 ≤ k) (h2 : k < 2333) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2332 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2332_ok
theorem cr_2331_2333 (k : ℕ) (h1 : 2331 ≤ k) (h2 : k < 2333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2332 then cr_2331_2332 k h1 h else cr_2332_2333 k (by omega) h2
theorem cr_2330_2333 (k : ℕ) (h1 : 2330 ≤ k) (h2 : k < 2333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2331 then cr_2330_2331 k h1 h else cr_2331_2333 k (by omega) h2
theorem cr_2328_2333 (k : ℕ) (h1 : 2328 ≤ k) (h2 : k < 2333) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2330 then cr_2328_2330 k h1 h else cr_2330_2333 k (by omega) h2
theorem cr_2333_2334 (k : ℕ) (h1 : 2333 ≤ k) (h2 : k < 2334) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2333 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2333_ok
theorem cr_2334_2335 (k : ℕ) (h1 : 2334 ≤ k) (h2 : k < 2335) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2334 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2334_ok
theorem cr_2335_2336 (k : ℕ) (h1 : 2335 ≤ k) (h2 : k < 2336) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2335 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2335_ok
theorem cr_2334_2336 (k : ℕ) (h1 : 2334 ≤ k) (h2 : k < 2336) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2335 then cr_2334_2335 k h1 h else cr_2335_2336 k (by omega) h2
theorem cr_2333_2336 (k : ℕ) (h1 : 2333 ≤ k) (h2 : k < 2336) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2334 then cr_2333_2334 k h1 h else cr_2334_2336 k (by omega) h2
theorem cr_2336_2337 (k : ℕ) (h1 : 2336 ≤ k) (h2 : k < 2337) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2336 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2336_ok
theorem cr_2337_2338 (k : ℕ) (h1 : 2337 ≤ k) (h2 : k < 2338) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2337 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2337_ok
theorem cr_2338_2339 (k : ℕ) (h1 : 2338 ≤ k) (h2 : k < 2339) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2338 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2338_ok
theorem cr_2337_2339 (k : ℕ) (h1 : 2337 ≤ k) (h2 : k < 2339) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2338 then cr_2337_2338 k h1 h else cr_2338_2339 k (by omega) h2
theorem cr_2336_2339 (k : ℕ) (h1 : 2336 ≤ k) (h2 : k < 2339) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2337 then cr_2336_2337 k h1 h else cr_2337_2339 k (by omega) h2
theorem cr_2333_2339 (k : ℕ) (h1 : 2333 ≤ k) (h2 : k < 2339) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2336 then cr_2333_2336 k h1 h else cr_2336_2339 k (by omega) h2
theorem cr_2328_2339 (k : ℕ) (h1 : 2328 ≤ k) (h2 : k < 2339) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2333 then cr_2328_2333 k h1 h else cr_2333_2339 k (by omega) h2
theorem cr_2318_2339 (k : ℕ) (h1 : 2318 ≤ k) (h2 : k < 2339) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2328 then cr_2318_2328 k h1 h else cr_2328_2339 k (by omega) h2
theorem cr_2298_2339 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2339) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2318 then cr_2298_2318 k h1 h else cr_2318_2339 k (by omega) h2
theorem cr_2339_2340 (k : ℕ) (h1 : 2339 ≤ k) (h2 : k < 2340) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2339 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2339_ok
theorem cr_2340_2341 (k : ℕ) (h1 : 2340 ≤ k) (h2 : k < 2341) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2340 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2340_ok
theorem cr_2339_2341 (k : ℕ) (h1 : 2339 ≤ k) (h2 : k < 2341) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2340 then cr_2339_2340 k h1 h else cr_2340_2341 k (by omega) h2
theorem cr_2341_2342 (k : ℕ) (h1 : 2341 ≤ k) (h2 : k < 2342) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2341 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2341_ok
theorem cr_2342_2343 (k : ℕ) (h1 : 2342 ≤ k) (h2 : k < 2343) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2342 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2342_ok
theorem cr_2343_2344 (k : ℕ) (h1 : 2343 ≤ k) (h2 : k < 2344) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2343 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2343_ok
theorem cr_2342_2344 (k : ℕ) (h1 : 2342 ≤ k) (h2 : k < 2344) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2343 then cr_2342_2343 k h1 h else cr_2343_2344 k (by omega) h2
theorem cr_2341_2344 (k : ℕ) (h1 : 2341 ≤ k) (h2 : k < 2344) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2342 then cr_2341_2342 k h1 h else cr_2342_2344 k (by omega) h2
theorem cr_2339_2344 (k : ℕ) (h1 : 2339 ≤ k) (h2 : k < 2344) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2341 then cr_2339_2341 k h1 h else cr_2341_2344 k (by omega) h2
theorem cr_2344_2345 (k : ℕ) (h1 : 2344 ≤ k) (h2 : k < 2345) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2344 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2344_ok
theorem cr_2345_2346 (k : ℕ) (h1 : 2345 ≤ k) (h2 : k < 2346) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2345 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2345_ok
theorem cr_2344_2346 (k : ℕ) (h1 : 2344 ≤ k) (h2 : k < 2346) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2345 then cr_2344_2345 k h1 h else cr_2345_2346 k (by omega) h2
theorem cr_2346_2347 (k : ℕ) (h1 : 2346 ≤ k) (h2 : k < 2347) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2346 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2346_ok
theorem cr_2347_2348 (k : ℕ) (h1 : 2347 ≤ k) (h2 : k < 2348) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2347 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2347_ok
theorem cr_2348_2349 (k : ℕ) (h1 : 2348 ≤ k) (h2 : k < 2349) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2348 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2348_ok
theorem cr_2347_2349 (k : ℕ) (h1 : 2347 ≤ k) (h2 : k < 2349) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2348 then cr_2347_2348 k h1 h else cr_2348_2349 k (by omega) h2
theorem cr_2346_2349 (k : ℕ) (h1 : 2346 ≤ k) (h2 : k < 2349) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2347 then cr_2346_2347 k h1 h else cr_2347_2349 k (by omega) h2
theorem cr_2344_2349 (k : ℕ) (h1 : 2344 ≤ k) (h2 : k < 2349) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2346 then cr_2344_2346 k h1 h else cr_2346_2349 k (by omega) h2
theorem cr_2339_2349 (k : ℕ) (h1 : 2339 ≤ k) (h2 : k < 2349) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2344 then cr_2339_2344 k h1 h else cr_2344_2349 k (by omega) h2
theorem cr_2349_2350 (k : ℕ) (h1 : 2349 ≤ k) (h2 : k < 2350) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2349 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2349_ok
theorem cr_2350_2351 (k : ℕ) (h1 : 2350 ≤ k) (h2 : k < 2351) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2350 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2350_ok
theorem cr_2349_2351 (k : ℕ) (h1 : 2349 ≤ k) (h2 : k < 2351) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2350 then cr_2349_2350 k h1 h else cr_2350_2351 k (by omega) h2
theorem cr_2351_2352 (k : ℕ) (h1 : 2351 ≤ k) (h2 : k < 2352) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2351 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2351_ok
theorem cr_2352_2353 (k : ℕ) (h1 : 2352 ≤ k) (h2 : k < 2353) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2352 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2352_ok
theorem cr_2353_2354 (k : ℕ) (h1 : 2353 ≤ k) (h2 : k < 2354) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2353 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2353_ok
theorem cr_2352_2354 (k : ℕ) (h1 : 2352 ≤ k) (h2 : k < 2354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2353 then cr_2352_2353 k h1 h else cr_2353_2354 k (by omega) h2
theorem cr_2351_2354 (k : ℕ) (h1 : 2351 ≤ k) (h2 : k < 2354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2352 then cr_2351_2352 k h1 h else cr_2352_2354 k (by omega) h2
theorem cr_2349_2354 (k : ℕ) (h1 : 2349 ≤ k) (h2 : k < 2354) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2351 then cr_2349_2351 k h1 h else cr_2351_2354 k (by omega) h2
theorem cr_2354_2355 (k : ℕ) (h1 : 2354 ≤ k) (h2 : k < 2355) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2354 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2354_ok
theorem cr_2355_2356 (k : ℕ) (h1 : 2355 ≤ k) (h2 : k < 2356) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2355 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2355_ok
theorem cr_2354_2356 (k : ℕ) (h1 : 2354 ≤ k) (h2 : k < 2356) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2355 then cr_2354_2355 k h1 h else cr_2355_2356 k (by omega) h2
theorem cr_2356_2357 (k : ℕ) (h1 : 2356 ≤ k) (h2 : k < 2357) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2356 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2356_ok
theorem cr_2357_2358 (k : ℕ) (h1 : 2357 ≤ k) (h2 : k < 2358) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2357 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2357_ok
theorem cr_2358_2359 (k : ℕ) (h1 : 2358 ≤ k) (h2 : k < 2359) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2358 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2358_ok
theorem cr_2357_2359 (k : ℕ) (h1 : 2357 ≤ k) (h2 : k < 2359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2358 then cr_2357_2358 k h1 h else cr_2358_2359 k (by omega) h2
theorem cr_2356_2359 (k : ℕ) (h1 : 2356 ≤ k) (h2 : k < 2359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2357 then cr_2356_2357 k h1 h else cr_2357_2359 k (by omega) h2
theorem cr_2354_2359 (k : ℕ) (h1 : 2354 ≤ k) (h2 : k < 2359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2356 then cr_2354_2356 k h1 h else cr_2356_2359 k (by omega) h2
theorem cr_2349_2359 (k : ℕ) (h1 : 2349 ≤ k) (h2 : k < 2359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2354 then cr_2349_2354 k h1 h else cr_2354_2359 k (by omega) h2
theorem cr_2339_2359 (k : ℕ) (h1 : 2339 ≤ k) (h2 : k < 2359) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2349 then cr_2339_2349 k h1 h else cr_2349_2359 k (by omega) h2
theorem cr_2359_2360 (k : ℕ) (h1 : 2359 ≤ k) (h2 : k < 2360) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2359 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2359_ok
theorem cr_2360_2361 (k : ℕ) (h1 : 2360 ≤ k) (h2 : k < 2361) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2360 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2360_ok
theorem cr_2359_2361 (k : ℕ) (h1 : 2359 ≤ k) (h2 : k < 2361) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2360 then cr_2359_2360 k h1 h else cr_2360_2361 k (by omega) h2
theorem cr_2361_2362 (k : ℕ) (h1 : 2361 ≤ k) (h2 : k < 2362) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2361 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2361_ok
theorem cr_2362_2363 (k : ℕ) (h1 : 2362 ≤ k) (h2 : k < 2363) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2362 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2362_ok
theorem cr_2363_2364 (k : ℕ) (h1 : 2363 ≤ k) (h2 : k < 2364) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2363 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2363_ok
theorem cr_2362_2364 (k : ℕ) (h1 : 2362 ≤ k) (h2 : k < 2364) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2363 then cr_2362_2363 k h1 h else cr_2363_2364 k (by omega) h2
theorem cr_2361_2364 (k : ℕ) (h1 : 2361 ≤ k) (h2 : k < 2364) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2362 then cr_2361_2362 k h1 h else cr_2362_2364 k (by omega) h2
theorem cr_2359_2364 (k : ℕ) (h1 : 2359 ≤ k) (h2 : k < 2364) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2361 then cr_2359_2361 k h1 h else cr_2361_2364 k (by omega) h2
theorem cr_2364_2365 (k : ℕ) (h1 : 2364 ≤ k) (h2 : k < 2365) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2364 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2364_ok
theorem cr_2365_2366 (k : ℕ) (h1 : 2365 ≤ k) (h2 : k < 2366) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2365 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2365_ok
theorem cr_2364_2366 (k : ℕ) (h1 : 2364 ≤ k) (h2 : k < 2366) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2365 then cr_2364_2365 k h1 h else cr_2365_2366 k (by omega) h2
theorem cr_2366_2367 (k : ℕ) (h1 : 2366 ≤ k) (h2 : k < 2367) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2366 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2366_ok
theorem cr_2367_2368 (k : ℕ) (h1 : 2367 ≤ k) (h2 : k < 2368) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2367 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2367_ok
theorem cr_2368_2369 (k : ℕ) (h1 : 2368 ≤ k) (h2 : k < 2369) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2368 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2368_ok
theorem cr_2367_2369 (k : ℕ) (h1 : 2367 ≤ k) (h2 : k < 2369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2368 then cr_2367_2368 k h1 h else cr_2368_2369 k (by omega) h2
theorem cr_2366_2369 (k : ℕ) (h1 : 2366 ≤ k) (h2 : k < 2369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2367 then cr_2366_2367 k h1 h else cr_2367_2369 k (by omega) h2
theorem cr_2364_2369 (k : ℕ) (h1 : 2364 ≤ k) (h2 : k < 2369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2366 then cr_2364_2366 k h1 h else cr_2366_2369 k (by omega) h2
theorem cr_2359_2369 (k : ℕ) (h1 : 2359 ≤ k) (h2 : k < 2369) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2364 then cr_2359_2364 k h1 h else cr_2364_2369 k (by omega) h2
theorem cr_2369_2370 (k : ℕ) (h1 : 2369 ≤ k) (h2 : k < 2370) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2369 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2369_ok
theorem cr_2370_2371 (k : ℕ) (h1 : 2370 ≤ k) (h2 : k < 2371) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2370 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2370_ok
theorem cr_2369_2371 (k : ℕ) (h1 : 2369 ≤ k) (h2 : k < 2371) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2370 then cr_2369_2370 k h1 h else cr_2370_2371 k (by omega) h2
theorem cr_2371_2372 (k : ℕ) (h1 : 2371 ≤ k) (h2 : k < 2372) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2371 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2371_ok
theorem cr_2372_2373 (k : ℕ) (h1 : 2372 ≤ k) (h2 : k < 2373) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2372 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2372_ok
theorem cr_2373_2374 (k : ℕ) (h1 : 2373 ≤ k) (h2 : k < 2374) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2373 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2373_ok
theorem cr_2372_2374 (k : ℕ) (h1 : 2372 ≤ k) (h2 : k < 2374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2373 then cr_2372_2373 k h1 h else cr_2373_2374 k (by omega) h2
theorem cr_2371_2374 (k : ℕ) (h1 : 2371 ≤ k) (h2 : k < 2374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2372 then cr_2371_2372 k h1 h else cr_2372_2374 k (by omega) h2
theorem cr_2369_2374 (k : ℕ) (h1 : 2369 ≤ k) (h2 : k < 2374) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2371 then cr_2369_2371 k h1 h else cr_2371_2374 k (by omega) h2
theorem cr_2374_2375 (k : ℕ) (h1 : 2374 ≤ k) (h2 : k < 2375) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2374 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2374_ok
theorem cr_2375_2376 (k : ℕ) (h1 : 2375 ≤ k) (h2 : k < 2376) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2375 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2375_ok
theorem cr_2376_2377 (k : ℕ) (h1 : 2376 ≤ k) (h2 : k < 2377) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2376 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2376_ok
theorem cr_2375_2377 (k : ℕ) (h1 : 2375 ≤ k) (h2 : k < 2377) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2376 then cr_2375_2376 k h1 h else cr_2376_2377 k (by omega) h2
theorem cr_2374_2377 (k : ℕ) (h1 : 2374 ≤ k) (h2 : k < 2377) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2375 then cr_2374_2375 k h1 h else cr_2375_2377 k (by omega) h2
theorem cr_2377_2378 (k : ℕ) (h1 : 2377 ≤ k) (h2 : k < 2378) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2377 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2377_ok
theorem cr_2378_2379 (k : ℕ) (h1 : 2378 ≤ k) (h2 : k < 2379) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2378 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2378_ok
theorem cr_2379_2380 (k : ℕ) (h1 : 2379 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2379 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2379_ok
theorem cr_2378_2380 (k : ℕ) (h1 : 2378 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2379 then cr_2378_2379 k h1 h else cr_2379_2380 k (by omega) h2
theorem cr_2377_2380 (k : ℕ) (h1 : 2377 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2378 then cr_2377_2378 k h1 h else cr_2378_2380 k (by omega) h2
theorem cr_2374_2380 (k : ℕ) (h1 : 2374 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2377 then cr_2374_2377 k h1 h else cr_2377_2380 k (by omega) h2
theorem cr_2369_2380 (k : ℕ) (h1 : 2369 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2374 then cr_2369_2374 k h1 h else cr_2374_2380 k (by omega) h2
theorem cr_2359_2380 (k : ℕ) (h1 : 2359 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2369 then cr_2359_2369 k h1 h else cr_2369_2380 k (by omega) h2
theorem cr_2339_2380 (k : ℕ) (h1 : 2339 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2359 then cr_2339_2359 k h1 h else cr_2359_2380 k (by omega) h2
theorem cr_2298_2380 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2380) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2339 then cr_2298_2339 k h1 h else cr_2339_2380 k (by omega) h2
theorem cr_2380_2381 (k : ℕ) (h1 : 2380 ≤ k) (h2 : k < 2381) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2380 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2380_ok
theorem cr_2381_2382 (k : ℕ) (h1 : 2381 ≤ k) (h2 : k < 2382) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2381 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2381_ok
theorem cr_2380_2382 (k : ℕ) (h1 : 2380 ≤ k) (h2 : k < 2382) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2381 then cr_2380_2381 k h1 h else cr_2381_2382 k (by omega) h2
theorem cr_2382_2383 (k : ℕ) (h1 : 2382 ≤ k) (h2 : k < 2383) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2382 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2382_ok
theorem cr_2383_2384 (k : ℕ) (h1 : 2383 ≤ k) (h2 : k < 2384) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2383 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2383_ok
theorem cr_2384_2385 (k : ℕ) (h1 : 2384 ≤ k) (h2 : k < 2385) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2384 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2384_ok
theorem cr_2383_2385 (k : ℕ) (h1 : 2383 ≤ k) (h2 : k < 2385) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2384 then cr_2383_2384 k h1 h else cr_2384_2385 k (by omega) h2
theorem cr_2382_2385 (k : ℕ) (h1 : 2382 ≤ k) (h2 : k < 2385) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2383 then cr_2382_2383 k h1 h else cr_2383_2385 k (by omega) h2
theorem cr_2380_2385 (k : ℕ) (h1 : 2380 ≤ k) (h2 : k < 2385) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2382 then cr_2380_2382 k h1 h else cr_2382_2385 k (by omega) h2
theorem cr_2385_2386 (k : ℕ) (h1 : 2385 ≤ k) (h2 : k < 2386) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2385 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2385_ok
theorem cr_2386_2387 (k : ℕ) (h1 : 2386 ≤ k) (h2 : k < 2387) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2386 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2386_ok
theorem cr_2385_2387 (k : ℕ) (h1 : 2385 ≤ k) (h2 : k < 2387) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2386 then cr_2385_2386 k h1 h else cr_2386_2387 k (by omega) h2
theorem cr_2387_2388 (k : ℕ) (h1 : 2387 ≤ k) (h2 : k < 2388) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2387 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2387_ok
theorem cr_2388_2389 (k : ℕ) (h1 : 2388 ≤ k) (h2 : k < 2389) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2388 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2388_ok
theorem cr_2389_2390 (k : ℕ) (h1 : 2389 ≤ k) (h2 : k < 2390) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2389 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2389_ok
theorem cr_2388_2390 (k : ℕ) (h1 : 2388 ≤ k) (h2 : k < 2390) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2389 then cr_2388_2389 k h1 h else cr_2389_2390 k (by omega) h2
theorem cr_2387_2390 (k : ℕ) (h1 : 2387 ≤ k) (h2 : k < 2390) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2388 then cr_2387_2388 k h1 h else cr_2388_2390 k (by omega) h2
theorem cr_2385_2390 (k : ℕ) (h1 : 2385 ≤ k) (h2 : k < 2390) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2387 then cr_2385_2387 k h1 h else cr_2387_2390 k (by omega) h2
theorem cr_2380_2390 (k : ℕ) (h1 : 2380 ≤ k) (h2 : k < 2390) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2385 then cr_2380_2385 k h1 h else cr_2385_2390 k (by omega) h2
theorem cr_2390_2391 (k : ℕ) (h1 : 2390 ≤ k) (h2 : k < 2391) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2390 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2390_ok
theorem cr_2391_2392 (k : ℕ) (h1 : 2391 ≤ k) (h2 : k < 2392) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2391 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2391_ok
theorem cr_2390_2392 (k : ℕ) (h1 : 2390 ≤ k) (h2 : k < 2392) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2391 then cr_2390_2391 k h1 h else cr_2391_2392 k (by omega) h2
theorem cr_2392_2393 (k : ℕ) (h1 : 2392 ≤ k) (h2 : k < 2393) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2392 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2392_ok
theorem cr_2393_2394 (k : ℕ) (h1 : 2393 ≤ k) (h2 : k < 2394) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2393 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2393_ok
theorem cr_2394_2395 (k : ℕ) (h1 : 2394 ≤ k) (h2 : k < 2395) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2394 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2394_ok
theorem cr_2393_2395 (k : ℕ) (h1 : 2393 ≤ k) (h2 : k < 2395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2394 then cr_2393_2394 k h1 h else cr_2394_2395 k (by omega) h2
theorem cr_2392_2395 (k : ℕ) (h1 : 2392 ≤ k) (h2 : k < 2395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2393 then cr_2392_2393 k h1 h else cr_2393_2395 k (by omega) h2
theorem cr_2390_2395 (k : ℕ) (h1 : 2390 ≤ k) (h2 : k < 2395) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2392 then cr_2390_2392 k h1 h else cr_2392_2395 k (by omega) h2
theorem cr_2395_2396 (k : ℕ) (h1 : 2395 ≤ k) (h2 : k < 2396) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2395 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2395_ok
theorem cr_2396_2397 (k : ℕ) (h1 : 2396 ≤ k) (h2 : k < 2397) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2396 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2396_ok
theorem cr_2395_2397 (k : ℕ) (h1 : 2395 ≤ k) (h2 : k < 2397) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2396 then cr_2395_2396 k h1 h else cr_2396_2397 k (by omega) h2
theorem cr_2397_2398 (k : ℕ) (h1 : 2397 ≤ k) (h2 : k < 2398) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2397 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2397_ok
theorem cr_2398_2399 (k : ℕ) (h1 : 2398 ≤ k) (h2 : k < 2399) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2398 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2398_ok
theorem cr_2399_2400 (k : ℕ) (h1 : 2399 ≤ k) (h2 : k < 2400) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2399 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2399_ok
theorem cr_2398_2400 (k : ℕ) (h1 : 2398 ≤ k) (h2 : k < 2400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2399 then cr_2398_2399 k h1 h else cr_2399_2400 k (by omega) h2
theorem cr_2397_2400 (k : ℕ) (h1 : 2397 ≤ k) (h2 : k < 2400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2398 then cr_2397_2398 k h1 h else cr_2398_2400 k (by omega) h2
theorem cr_2395_2400 (k : ℕ) (h1 : 2395 ≤ k) (h2 : k < 2400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2397 then cr_2395_2397 k h1 h else cr_2397_2400 k (by omega) h2
theorem cr_2390_2400 (k : ℕ) (h1 : 2390 ≤ k) (h2 : k < 2400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2395 then cr_2390_2395 k h1 h else cr_2395_2400 k (by omega) h2
theorem cr_2380_2400 (k : ℕ) (h1 : 2380 ≤ k) (h2 : k < 2400) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2390 then cr_2380_2390 k h1 h else cr_2390_2400 k (by omega) h2
theorem cr_2400_2401 (k : ℕ) (h1 : 2400 ≤ k) (h2 : k < 2401) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2400 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2400_ok
theorem cr_2401_2402 (k : ℕ) (h1 : 2401 ≤ k) (h2 : k < 2402) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2401 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2401_ok
theorem cr_2400_2402 (k : ℕ) (h1 : 2400 ≤ k) (h2 : k < 2402) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2401 then cr_2400_2401 k h1 h else cr_2401_2402 k (by omega) h2
theorem cr_2402_2403 (k : ℕ) (h1 : 2402 ≤ k) (h2 : k < 2403) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2402 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2402_ok
theorem cr_2403_2404 (k : ℕ) (h1 : 2403 ≤ k) (h2 : k < 2404) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2403 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2403_ok
theorem cr_2404_2405 (k : ℕ) (h1 : 2404 ≤ k) (h2 : k < 2405) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2404 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2404_ok
theorem cr_2403_2405 (k : ℕ) (h1 : 2403 ≤ k) (h2 : k < 2405) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2404 then cr_2403_2404 k h1 h else cr_2404_2405 k (by omega) h2
theorem cr_2402_2405 (k : ℕ) (h1 : 2402 ≤ k) (h2 : k < 2405) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2403 then cr_2402_2403 k h1 h else cr_2403_2405 k (by omega) h2
theorem cr_2400_2405 (k : ℕ) (h1 : 2400 ≤ k) (h2 : k < 2405) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2402 then cr_2400_2402 k h1 h else cr_2402_2405 k (by omega) h2
theorem cr_2405_2406 (k : ℕ) (h1 : 2405 ≤ k) (h2 : k < 2406) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2405 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2405_ok
theorem cr_2406_2407 (k : ℕ) (h1 : 2406 ≤ k) (h2 : k < 2407) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2406 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2406_ok
theorem cr_2405_2407 (k : ℕ) (h1 : 2405 ≤ k) (h2 : k < 2407) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2406 then cr_2405_2406 k h1 h else cr_2406_2407 k (by omega) h2
theorem cr_2407_2408 (k : ℕ) (h1 : 2407 ≤ k) (h2 : k < 2408) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2407 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2407_ok
theorem cr_2408_2409 (k : ℕ) (h1 : 2408 ≤ k) (h2 : k < 2409) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2408 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2408_ok
theorem cr_2409_2410 (k : ℕ) (h1 : 2409 ≤ k) (h2 : k < 2410) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2409 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2409_ok
theorem cr_2408_2410 (k : ℕ) (h1 : 2408 ≤ k) (h2 : k < 2410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2409 then cr_2408_2409 k h1 h else cr_2409_2410 k (by omega) h2
theorem cr_2407_2410 (k : ℕ) (h1 : 2407 ≤ k) (h2 : k < 2410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2408 then cr_2407_2408 k h1 h else cr_2408_2410 k (by omega) h2
theorem cr_2405_2410 (k : ℕ) (h1 : 2405 ≤ k) (h2 : k < 2410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2407 then cr_2405_2407 k h1 h else cr_2407_2410 k (by omega) h2
theorem cr_2400_2410 (k : ℕ) (h1 : 2400 ≤ k) (h2 : k < 2410) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2405 then cr_2400_2405 k h1 h else cr_2405_2410 k (by omega) h2
theorem cr_2410_2411 (k : ℕ) (h1 : 2410 ≤ k) (h2 : k < 2411) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2410 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2410_ok
theorem cr_2411_2412 (k : ℕ) (h1 : 2411 ≤ k) (h2 : k < 2412) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2411 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2411_ok
theorem cr_2410_2412 (k : ℕ) (h1 : 2410 ≤ k) (h2 : k < 2412) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2411 then cr_2410_2411 k h1 h else cr_2411_2412 k (by omega) h2
theorem cr_2412_2413 (k : ℕ) (h1 : 2412 ≤ k) (h2 : k < 2413) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2412 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2412_ok
theorem cr_2413_2414 (k : ℕ) (h1 : 2413 ≤ k) (h2 : k < 2414) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2413 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2413_ok
theorem cr_2414_2415 (k : ℕ) (h1 : 2414 ≤ k) (h2 : k < 2415) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2414 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2414_ok
theorem cr_2413_2415 (k : ℕ) (h1 : 2413 ≤ k) (h2 : k < 2415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2414 then cr_2413_2414 k h1 h else cr_2414_2415 k (by omega) h2
theorem cr_2412_2415 (k : ℕ) (h1 : 2412 ≤ k) (h2 : k < 2415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2413 then cr_2412_2413 k h1 h else cr_2413_2415 k (by omega) h2
theorem cr_2410_2415 (k : ℕ) (h1 : 2410 ≤ k) (h2 : k < 2415) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2412 then cr_2410_2412 k h1 h else cr_2412_2415 k (by omega) h2
theorem cr_2415_2416 (k : ℕ) (h1 : 2415 ≤ k) (h2 : k < 2416) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2415 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2415_ok
theorem cr_2416_2417 (k : ℕ) (h1 : 2416 ≤ k) (h2 : k < 2417) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2416 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2416_ok
theorem cr_2417_2418 (k : ℕ) (h1 : 2417 ≤ k) (h2 : k < 2418) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2417 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2417_ok
theorem cr_2416_2418 (k : ℕ) (h1 : 2416 ≤ k) (h2 : k < 2418) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2417 then cr_2416_2417 k h1 h else cr_2417_2418 k (by omega) h2
theorem cr_2415_2418 (k : ℕ) (h1 : 2415 ≤ k) (h2 : k < 2418) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2416 then cr_2415_2416 k h1 h else cr_2416_2418 k (by omega) h2
theorem cr_2418_2419 (k : ℕ) (h1 : 2418 ≤ k) (h2 : k < 2419) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2418 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2418_ok
theorem cr_2419_2420 (k : ℕ) (h1 : 2419 ≤ k) (h2 : k < 2420) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2419 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2419_ok
theorem cr_2420_2421 (k : ℕ) (h1 : 2420 ≤ k) (h2 : k < 2421) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2420 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2420_ok
theorem cr_2419_2421 (k : ℕ) (h1 : 2419 ≤ k) (h2 : k < 2421) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2420 then cr_2419_2420 k h1 h else cr_2420_2421 k (by omega) h2
theorem cr_2418_2421 (k : ℕ) (h1 : 2418 ≤ k) (h2 : k < 2421) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2419 then cr_2418_2419 k h1 h else cr_2419_2421 k (by omega) h2
theorem cr_2415_2421 (k : ℕ) (h1 : 2415 ≤ k) (h2 : k < 2421) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2418 then cr_2415_2418 k h1 h else cr_2418_2421 k (by omega) h2
theorem cr_2410_2421 (k : ℕ) (h1 : 2410 ≤ k) (h2 : k < 2421) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2415 then cr_2410_2415 k h1 h else cr_2415_2421 k (by omega) h2
theorem cr_2400_2421 (k : ℕ) (h1 : 2400 ≤ k) (h2 : k < 2421) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2410 then cr_2400_2410 k h1 h else cr_2410_2421 k (by omega) h2
theorem cr_2380_2421 (k : ℕ) (h1 : 2380 ≤ k) (h2 : k < 2421) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2400 then cr_2380_2400 k h1 h else cr_2400_2421 k (by omega) h2
theorem cr_2421_2422 (k : ℕ) (h1 : 2421 ≤ k) (h2 : k < 2422) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2421 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2421_ok
theorem cr_2422_2423 (k : ℕ) (h1 : 2422 ≤ k) (h2 : k < 2423) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2422 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2422_ok
theorem cr_2421_2423 (k : ℕ) (h1 : 2421 ≤ k) (h2 : k < 2423) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2422 then cr_2421_2422 k h1 h else cr_2422_2423 k (by omega) h2
theorem cr_2423_2424 (k : ℕ) (h1 : 2423 ≤ k) (h2 : k < 2424) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2423 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2423_ok
theorem cr_2424_2425 (k : ℕ) (h1 : 2424 ≤ k) (h2 : k < 2425) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2424 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2424_ok
theorem cr_2425_2426 (k : ℕ) (h1 : 2425 ≤ k) (h2 : k < 2426) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2425 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2425_ok
theorem cr_2424_2426 (k : ℕ) (h1 : 2424 ≤ k) (h2 : k < 2426) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2425 then cr_2424_2425 k h1 h else cr_2425_2426 k (by omega) h2
theorem cr_2423_2426 (k : ℕ) (h1 : 2423 ≤ k) (h2 : k < 2426) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2424 then cr_2423_2424 k h1 h else cr_2424_2426 k (by omega) h2
theorem cr_2421_2426 (k : ℕ) (h1 : 2421 ≤ k) (h2 : k < 2426) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2423 then cr_2421_2423 k h1 h else cr_2423_2426 k (by omega) h2
theorem cr_2426_2427 (k : ℕ) (h1 : 2426 ≤ k) (h2 : k < 2427) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2426 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2426_ok
theorem cr_2427_2428 (k : ℕ) (h1 : 2427 ≤ k) (h2 : k < 2428) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2427 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2427_ok
theorem cr_2426_2428 (k : ℕ) (h1 : 2426 ≤ k) (h2 : k < 2428) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2427 then cr_2426_2427 k h1 h else cr_2427_2428 k (by omega) h2
theorem cr_2428_2429 (k : ℕ) (h1 : 2428 ≤ k) (h2 : k < 2429) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2428 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2428_ok
theorem cr_2429_2430 (k : ℕ) (h1 : 2429 ≤ k) (h2 : k < 2430) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2429 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2429_ok
theorem cr_2430_2431 (k : ℕ) (h1 : 2430 ≤ k) (h2 : k < 2431) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2430 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2430_ok
theorem cr_2429_2431 (k : ℕ) (h1 : 2429 ≤ k) (h2 : k < 2431) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2430 then cr_2429_2430 k h1 h else cr_2430_2431 k (by omega) h2
theorem cr_2428_2431 (k : ℕ) (h1 : 2428 ≤ k) (h2 : k < 2431) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2429 then cr_2428_2429 k h1 h else cr_2429_2431 k (by omega) h2
theorem cr_2426_2431 (k : ℕ) (h1 : 2426 ≤ k) (h2 : k < 2431) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2428 then cr_2426_2428 k h1 h else cr_2428_2431 k (by omega) h2
theorem cr_2421_2431 (k : ℕ) (h1 : 2421 ≤ k) (h2 : k < 2431) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2426 then cr_2421_2426 k h1 h else cr_2426_2431 k (by omega) h2
theorem cr_2431_2432 (k : ℕ) (h1 : 2431 ≤ k) (h2 : k < 2432) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2431 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2431_ok
theorem cr_2432_2433 (k : ℕ) (h1 : 2432 ≤ k) (h2 : k < 2433) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2432 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2432_ok
theorem cr_2431_2433 (k : ℕ) (h1 : 2431 ≤ k) (h2 : k < 2433) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2432 then cr_2431_2432 k h1 h else cr_2432_2433 k (by omega) h2
theorem cr_2433_2434 (k : ℕ) (h1 : 2433 ≤ k) (h2 : k < 2434) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2433 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2433_ok
theorem cr_2434_2435 (k : ℕ) (h1 : 2434 ≤ k) (h2 : k < 2435) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2434 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2434_ok
theorem cr_2435_2436 (k : ℕ) (h1 : 2435 ≤ k) (h2 : k < 2436) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2435 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2435_ok
theorem cr_2434_2436 (k : ℕ) (h1 : 2434 ≤ k) (h2 : k < 2436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2435 then cr_2434_2435 k h1 h else cr_2435_2436 k (by omega) h2
theorem cr_2433_2436 (k : ℕ) (h1 : 2433 ≤ k) (h2 : k < 2436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2434 then cr_2433_2434 k h1 h else cr_2434_2436 k (by omega) h2
theorem cr_2431_2436 (k : ℕ) (h1 : 2431 ≤ k) (h2 : k < 2436) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2433 then cr_2431_2433 k h1 h else cr_2433_2436 k (by omega) h2
theorem cr_2436_2437 (k : ℕ) (h1 : 2436 ≤ k) (h2 : k < 2437) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2436 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2436_ok
theorem cr_2437_2438 (k : ℕ) (h1 : 2437 ≤ k) (h2 : k < 2438) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2437 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2437_ok
theorem cr_2436_2438 (k : ℕ) (h1 : 2436 ≤ k) (h2 : k < 2438) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2437 then cr_2436_2437 k h1 h else cr_2437_2438 k (by omega) h2
theorem cr_2438_2439 (k : ℕ) (h1 : 2438 ≤ k) (h2 : k < 2439) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2438 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2438_ok
theorem cr_2439_2440 (k : ℕ) (h1 : 2439 ≤ k) (h2 : k < 2440) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2439 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2439_ok
theorem cr_2440_2441 (k : ℕ) (h1 : 2440 ≤ k) (h2 : k < 2441) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2440 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2440_ok
theorem cr_2439_2441 (k : ℕ) (h1 : 2439 ≤ k) (h2 : k < 2441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2440 then cr_2439_2440 k h1 h else cr_2440_2441 k (by omega) h2
theorem cr_2438_2441 (k : ℕ) (h1 : 2438 ≤ k) (h2 : k < 2441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2439 then cr_2438_2439 k h1 h else cr_2439_2441 k (by omega) h2
theorem cr_2436_2441 (k : ℕ) (h1 : 2436 ≤ k) (h2 : k < 2441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2438 then cr_2436_2438 k h1 h else cr_2438_2441 k (by omega) h2
theorem cr_2431_2441 (k : ℕ) (h1 : 2431 ≤ k) (h2 : k < 2441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2436 then cr_2431_2436 k h1 h else cr_2436_2441 k (by omega) h2
theorem cr_2421_2441 (k : ℕ) (h1 : 2421 ≤ k) (h2 : k < 2441) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2431 then cr_2421_2431 k h1 h else cr_2431_2441 k (by omega) h2
theorem cr_2441_2442 (k : ℕ) (h1 : 2441 ≤ k) (h2 : k < 2442) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2441 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2441_ok
theorem cr_2442_2443 (k : ℕ) (h1 : 2442 ≤ k) (h2 : k < 2443) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2442 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2442_ok
theorem cr_2441_2443 (k : ℕ) (h1 : 2441 ≤ k) (h2 : k < 2443) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2442 then cr_2441_2442 k h1 h else cr_2442_2443 k (by omega) h2
theorem cr_2443_2444 (k : ℕ) (h1 : 2443 ≤ k) (h2 : k < 2444) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2443 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2443_ok
theorem cr_2444_2445 (k : ℕ) (h1 : 2444 ≤ k) (h2 : k < 2445) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2444 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2444_ok
theorem cr_2445_2446 (k : ℕ) (h1 : 2445 ≤ k) (h2 : k < 2446) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2445 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2445_ok
theorem cr_2444_2446 (k : ℕ) (h1 : 2444 ≤ k) (h2 : k < 2446) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2445 then cr_2444_2445 k h1 h else cr_2445_2446 k (by omega) h2
theorem cr_2443_2446 (k : ℕ) (h1 : 2443 ≤ k) (h2 : k < 2446) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2444 then cr_2443_2444 k h1 h else cr_2444_2446 k (by omega) h2
theorem cr_2441_2446 (k : ℕ) (h1 : 2441 ≤ k) (h2 : k < 2446) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2443 then cr_2441_2443 k h1 h else cr_2443_2446 k (by omega) h2
theorem cr_2446_2447 (k : ℕ) (h1 : 2446 ≤ k) (h2 : k < 2447) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2446 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2446_ok
theorem cr_2447_2448 (k : ℕ) (h1 : 2447 ≤ k) (h2 : k < 2448) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2447 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2447_ok
theorem cr_2446_2448 (k : ℕ) (h1 : 2446 ≤ k) (h2 : k < 2448) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2447 then cr_2446_2447 k h1 h else cr_2447_2448 k (by omega) h2
theorem cr_2448_2449 (k : ℕ) (h1 : 2448 ≤ k) (h2 : k < 2449) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2448 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2448_ok
theorem cr_2449_2450 (k : ℕ) (h1 : 2449 ≤ k) (h2 : k < 2450) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2449 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2449_ok
theorem cr_2450_2451 (k : ℕ) (h1 : 2450 ≤ k) (h2 : k < 2451) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2450 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2450_ok
theorem cr_2449_2451 (k : ℕ) (h1 : 2449 ≤ k) (h2 : k < 2451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2450 then cr_2449_2450 k h1 h else cr_2450_2451 k (by omega) h2
theorem cr_2448_2451 (k : ℕ) (h1 : 2448 ≤ k) (h2 : k < 2451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2449 then cr_2448_2449 k h1 h else cr_2449_2451 k (by omega) h2
theorem cr_2446_2451 (k : ℕ) (h1 : 2446 ≤ k) (h2 : k < 2451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2448 then cr_2446_2448 k h1 h else cr_2448_2451 k (by omega) h2
theorem cr_2441_2451 (k : ℕ) (h1 : 2441 ≤ k) (h2 : k < 2451) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2446 then cr_2441_2446 k h1 h else cr_2446_2451 k (by omega) h2
theorem cr_2451_2452 (k : ℕ) (h1 : 2451 ≤ k) (h2 : k < 2452) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2451 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2451_ok
theorem cr_2452_2453 (k : ℕ) (h1 : 2452 ≤ k) (h2 : k < 2453) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2452 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2452_ok
theorem cr_2451_2453 (k : ℕ) (h1 : 2451 ≤ k) (h2 : k < 2453) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2452 then cr_2451_2452 k h1 h else cr_2452_2453 k (by omega) h2
theorem cr_2453_2454 (k : ℕ) (h1 : 2453 ≤ k) (h2 : k < 2454) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2453 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2453_ok
theorem cr_2454_2455 (k : ℕ) (h1 : 2454 ≤ k) (h2 : k < 2455) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2454 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2454_ok
theorem cr_2455_2456 (k : ℕ) (h1 : 2455 ≤ k) (h2 : k < 2456) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2455 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2455_ok
theorem cr_2454_2456 (k : ℕ) (h1 : 2454 ≤ k) (h2 : k < 2456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2455 then cr_2454_2455 k h1 h else cr_2455_2456 k (by omega) h2
theorem cr_2453_2456 (k : ℕ) (h1 : 2453 ≤ k) (h2 : k < 2456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2454 then cr_2453_2454 k h1 h else cr_2454_2456 k (by omega) h2
theorem cr_2451_2456 (k : ℕ) (h1 : 2451 ≤ k) (h2 : k < 2456) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2453 then cr_2451_2453 k h1 h else cr_2453_2456 k (by omega) h2
theorem cr_2456_2457 (k : ℕ) (h1 : 2456 ≤ k) (h2 : k < 2457) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2456 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2456_ok
theorem cr_2457_2458 (k : ℕ) (h1 : 2457 ≤ k) (h2 : k < 2458) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2457 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2457_ok
theorem cr_2458_2459 (k : ℕ) (h1 : 2458 ≤ k) (h2 : k < 2459) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2458 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2458_ok
theorem cr_2457_2459 (k : ℕ) (h1 : 2457 ≤ k) (h2 : k < 2459) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2458 then cr_2457_2458 k h1 h else cr_2458_2459 k (by omega) h2
theorem cr_2456_2459 (k : ℕ) (h1 : 2456 ≤ k) (h2 : k < 2459) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2457 then cr_2456_2457 k h1 h else cr_2457_2459 k (by omega) h2
theorem cr_2459_2460 (k : ℕ) (h1 : 2459 ≤ k) (h2 : k < 2460) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2459 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2459_ok
theorem cr_2460_2461 (k : ℕ) (h1 : 2460 ≤ k) (h2 : k < 2461) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2460 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2460_ok
theorem cr_2461_2462 (k : ℕ) (h1 : 2461 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2461 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2461_ok
theorem cr_2460_2462 (k : ℕ) (h1 : 2460 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2461 then cr_2460_2461 k h1 h else cr_2461_2462 k (by omega) h2
theorem cr_2459_2462 (k : ℕ) (h1 : 2459 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2460 then cr_2459_2460 k h1 h else cr_2460_2462 k (by omega) h2
theorem cr_2456_2462 (k : ℕ) (h1 : 2456 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2459 then cr_2456_2459 k h1 h else cr_2459_2462 k (by omega) h2
theorem cr_2451_2462 (k : ℕ) (h1 : 2451 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2456 then cr_2451_2456 k h1 h else cr_2456_2462 k (by omega) h2
theorem cr_2441_2462 (k : ℕ) (h1 : 2441 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2451 then cr_2441_2451 k h1 h else cr_2451_2462 k (by omega) h2
theorem cr_2421_2462 (k : ℕ) (h1 : 2421 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2441 then cr_2421_2441 k h1 h else cr_2441_2462 k (by omega) h2
theorem cr_2380_2462 (k : ℕ) (h1 : 2380 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2421 then cr_2380_2421 k h1 h else cr_2421_2462 k (by omega) h2
theorem cr_2298_2462 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2462) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2380 then cr_2298_2380 k h1 h else cr_2380_2462 k (by omega) h2
theorem cr_2462_2463 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2463) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2462 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2462_ok
theorem cr_2463_2464 (k : ℕ) (h1 : 2463 ≤ k) (h2 : k < 2464) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2463 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2463_ok
theorem cr_2462_2464 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2464) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2463 then cr_2462_2463 k h1 h else cr_2463_2464 k (by omega) h2
theorem cr_2464_2465 (k : ℕ) (h1 : 2464 ≤ k) (h2 : k < 2465) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2464 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2464_ok
theorem cr_2465_2466 (k : ℕ) (h1 : 2465 ≤ k) (h2 : k < 2466) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2465 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2465_ok
theorem cr_2466_2467 (k : ℕ) (h1 : 2466 ≤ k) (h2 : k < 2467) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2466 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2466_ok
theorem cr_2465_2467 (k : ℕ) (h1 : 2465 ≤ k) (h2 : k < 2467) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2466 then cr_2465_2466 k h1 h else cr_2466_2467 k (by omega) h2
theorem cr_2464_2467 (k : ℕ) (h1 : 2464 ≤ k) (h2 : k < 2467) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2465 then cr_2464_2465 k h1 h else cr_2465_2467 k (by omega) h2
theorem cr_2462_2467 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2467) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2464 then cr_2462_2464 k h1 h else cr_2464_2467 k (by omega) h2
theorem cr_2467_2468 (k : ℕ) (h1 : 2467 ≤ k) (h2 : k < 2468) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2467 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2467_ok
theorem cr_2468_2469 (k : ℕ) (h1 : 2468 ≤ k) (h2 : k < 2469) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2468 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2468_ok
theorem cr_2467_2469 (k : ℕ) (h1 : 2467 ≤ k) (h2 : k < 2469) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2468 then cr_2467_2468 k h1 h else cr_2468_2469 k (by omega) h2
theorem cr_2469_2470 (k : ℕ) (h1 : 2469 ≤ k) (h2 : k < 2470) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2469 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2469_ok
theorem cr_2470_2471 (k : ℕ) (h1 : 2470 ≤ k) (h2 : k < 2471) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2470 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2470_ok
theorem cr_2471_2472 (k : ℕ) (h1 : 2471 ≤ k) (h2 : k < 2472) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2471 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2471_ok
theorem cr_2470_2472 (k : ℕ) (h1 : 2470 ≤ k) (h2 : k < 2472) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2471 then cr_2470_2471 k h1 h else cr_2471_2472 k (by omega) h2
theorem cr_2469_2472 (k : ℕ) (h1 : 2469 ≤ k) (h2 : k < 2472) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2470 then cr_2469_2470 k h1 h else cr_2470_2472 k (by omega) h2
theorem cr_2467_2472 (k : ℕ) (h1 : 2467 ≤ k) (h2 : k < 2472) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2469 then cr_2467_2469 k h1 h else cr_2469_2472 k (by omega) h2
theorem cr_2462_2472 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2472) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2467 then cr_2462_2467 k h1 h else cr_2467_2472 k (by omega) h2
theorem cr_2472_2473 (k : ℕ) (h1 : 2472 ≤ k) (h2 : k < 2473) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2472 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2472_ok
theorem cr_2473_2474 (k : ℕ) (h1 : 2473 ≤ k) (h2 : k < 2474) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2473 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2473_ok
theorem cr_2472_2474 (k : ℕ) (h1 : 2472 ≤ k) (h2 : k < 2474) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2473 then cr_2472_2473 k h1 h else cr_2473_2474 k (by omega) h2
theorem cr_2474_2475 (k : ℕ) (h1 : 2474 ≤ k) (h2 : k < 2475) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2474 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2474_ok
theorem cr_2475_2476 (k : ℕ) (h1 : 2475 ≤ k) (h2 : k < 2476) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2475 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2475_ok
theorem cr_2476_2477 (k : ℕ) (h1 : 2476 ≤ k) (h2 : k < 2477) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2476 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2476_ok
theorem cr_2475_2477 (k : ℕ) (h1 : 2475 ≤ k) (h2 : k < 2477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2476 then cr_2475_2476 k h1 h else cr_2476_2477 k (by omega) h2
theorem cr_2474_2477 (k : ℕ) (h1 : 2474 ≤ k) (h2 : k < 2477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2475 then cr_2474_2475 k h1 h else cr_2475_2477 k (by omega) h2
theorem cr_2472_2477 (k : ℕ) (h1 : 2472 ≤ k) (h2 : k < 2477) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2474 then cr_2472_2474 k h1 h else cr_2474_2477 k (by omega) h2
theorem cr_2477_2478 (k : ℕ) (h1 : 2477 ≤ k) (h2 : k < 2478) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2477 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2477_ok
theorem cr_2478_2479 (k : ℕ) (h1 : 2478 ≤ k) (h2 : k < 2479) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2478 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2478_ok
theorem cr_2477_2479 (k : ℕ) (h1 : 2477 ≤ k) (h2 : k < 2479) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2478 then cr_2477_2478 k h1 h else cr_2478_2479 k (by omega) h2
theorem cr_2479_2480 (k : ℕ) (h1 : 2479 ≤ k) (h2 : k < 2480) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2479 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2479_ok
theorem cr_2480_2481 (k : ℕ) (h1 : 2480 ≤ k) (h2 : k < 2481) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2480 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2480_ok
theorem cr_2481_2482 (k : ℕ) (h1 : 2481 ≤ k) (h2 : k < 2482) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2481 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2481_ok
theorem cr_2480_2482 (k : ℕ) (h1 : 2480 ≤ k) (h2 : k < 2482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2481 then cr_2480_2481 k h1 h else cr_2481_2482 k (by omega) h2
theorem cr_2479_2482 (k : ℕ) (h1 : 2479 ≤ k) (h2 : k < 2482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2480 then cr_2479_2480 k h1 h else cr_2480_2482 k (by omega) h2
theorem cr_2477_2482 (k : ℕ) (h1 : 2477 ≤ k) (h2 : k < 2482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2479 then cr_2477_2479 k h1 h else cr_2479_2482 k (by omega) h2
theorem cr_2472_2482 (k : ℕ) (h1 : 2472 ≤ k) (h2 : k < 2482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2477 then cr_2472_2477 k h1 h else cr_2477_2482 k (by omega) h2
theorem cr_2462_2482 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2482) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2472 then cr_2462_2472 k h1 h else cr_2472_2482 k (by omega) h2
theorem cr_2482_2483 (k : ℕ) (h1 : 2482 ≤ k) (h2 : k < 2483) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2482 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2482_ok
theorem cr_2483_2484 (k : ℕ) (h1 : 2483 ≤ k) (h2 : k < 2484) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2483 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2483_ok
theorem cr_2482_2484 (k : ℕ) (h1 : 2482 ≤ k) (h2 : k < 2484) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2483 then cr_2482_2483 k h1 h else cr_2483_2484 k (by omega) h2
theorem cr_2484_2485 (k : ℕ) (h1 : 2484 ≤ k) (h2 : k < 2485) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2484 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2484_ok
theorem cr_2485_2486 (k : ℕ) (h1 : 2485 ≤ k) (h2 : k < 2486) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2485 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2485_ok
theorem cr_2486_2487 (k : ℕ) (h1 : 2486 ≤ k) (h2 : k < 2487) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2486 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2486_ok
theorem cr_2485_2487 (k : ℕ) (h1 : 2485 ≤ k) (h2 : k < 2487) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2486 then cr_2485_2486 k h1 h else cr_2486_2487 k (by omega) h2
theorem cr_2484_2487 (k : ℕ) (h1 : 2484 ≤ k) (h2 : k < 2487) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2485 then cr_2484_2485 k h1 h else cr_2485_2487 k (by omega) h2
theorem cr_2482_2487 (k : ℕ) (h1 : 2482 ≤ k) (h2 : k < 2487) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2484 then cr_2482_2484 k h1 h else cr_2484_2487 k (by omega) h2
theorem cr_2487_2488 (k : ℕ) (h1 : 2487 ≤ k) (h2 : k < 2488) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2487 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2487_ok
theorem cr_2488_2489 (k : ℕ) (h1 : 2488 ≤ k) (h2 : k < 2489) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2488 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2488_ok
theorem cr_2487_2489 (k : ℕ) (h1 : 2487 ≤ k) (h2 : k < 2489) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2488 then cr_2487_2488 k h1 h else cr_2488_2489 k (by omega) h2
theorem cr_2489_2490 (k : ℕ) (h1 : 2489 ≤ k) (h2 : k < 2490) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2489 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2489_ok
theorem cr_2490_2491 (k : ℕ) (h1 : 2490 ≤ k) (h2 : k < 2491) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2490 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2490_ok
theorem cr_2491_2492 (k : ℕ) (h1 : 2491 ≤ k) (h2 : k < 2492) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2491 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2491_ok
theorem cr_2490_2492 (k : ℕ) (h1 : 2490 ≤ k) (h2 : k < 2492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2491 then cr_2490_2491 k h1 h else cr_2491_2492 k (by omega) h2
theorem cr_2489_2492 (k : ℕ) (h1 : 2489 ≤ k) (h2 : k < 2492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2490 then cr_2489_2490 k h1 h else cr_2490_2492 k (by omega) h2
theorem cr_2487_2492 (k : ℕ) (h1 : 2487 ≤ k) (h2 : k < 2492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2489 then cr_2487_2489 k h1 h else cr_2489_2492 k (by omega) h2
theorem cr_2482_2492 (k : ℕ) (h1 : 2482 ≤ k) (h2 : k < 2492) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2487 then cr_2482_2487 k h1 h else cr_2487_2492 k (by omega) h2
theorem cr_2492_2493 (k : ℕ) (h1 : 2492 ≤ k) (h2 : k < 2493) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2492 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2492_ok
theorem cr_2493_2494 (k : ℕ) (h1 : 2493 ≤ k) (h2 : k < 2494) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2493 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2493_ok
theorem cr_2492_2494 (k : ℕ) (h1 : 2492 ≤ k) (h2 : k < 2494) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2493 then cr_2492_2493 k h1 h else cr_2493_2494 k (by omega) h2
theorem cr_2494_2495 (k : ℕ) (h1 : 2494 ≤ k) (h2 : k < 2495) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2494 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2494_ok
theorem cr_2495_2496 (k : ℕ) (h1 : 2495 ≤ k) (h2 : k < 2496) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2495 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2495_ok
theorem cr_2496_2497 (k : ℕ) (h1 : 2496 ≤ k) (h2 : k < 2497) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2496 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2496_ok
theorem cr_2495_2497 (k : ℕ) (h1 : 2495 ≤ k) (h2 : k < 2497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2496 then cr_2495_2496 k h1 h else cr_2496_2497 k (by omega) h2
theorem cr_2494_2497 (k : ℕ) (h1 : 2494 ≤ k) (h2 : k < 2497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2495 then cr_2494_2495 k h1 h else cr_2495_2497 k (by omega) h2
theorem cr_2492_2497 (k : ℕ) (h1 : 2492 ≤ k) (h2 : k < 2497) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2494 then cr_2492_2494 k h1 h else cr_2494_2497 k (by omega) h2
theorem cr_2497_2498 (k : ℕ) (h1 : 2497 ≤ k) (h2 : k < 2498) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2497 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2497_ok
theorem cr_2498_2499 (k : ℕ) (h1 : 2498 ≤ k) (h2 : k < 2499) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2498 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2498_ok
theorem cr_2499_2500 (k : ℕ) (h1 : 2499 ≤ k) (h2 : k < 2500) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2499 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2499_ok
theorem cr_2498_2500 (k : ℕ) (h1 : 2498 ≤ k) (h2 : k < 2500) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2499 then cr_2498_2499 k h1 h else cr_2499_2500 k (by omega) h2
theorem cr_2497_2500 (k : ℕ) (h1 : 2497 ≤ k) (h2 : k < 2500) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2498 then cr_2497_2498 k h1 h else cr_2498_2500 k (by omega) h2
theorem cr_2500_2501 (k : ℕ) (h1 : 2500 ≤ k) (h2 : k < 2501) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2500 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2500_ok
theorem cr_2501_2502 (k : ℕ) (h1 : 2501 ≤ k) (h2 : k < 2502) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2501 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2501_ok
theorem cr_2502_2503 (k : ℕ) (h1 : 2502 ≤ k) (h2 : k < 2503) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2502 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2502_ok
theorem cr_2501_2503 (k : ℕ) (h1 : 2501 ≤ k) (h2 : k < 2503) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2502 then cr_2501_2502 k h1 h else cr_2502_2503 k (by omega) h2
theorem cr_2500_2503 (k : ℕ) (h1 : 2500 ≤ k) (h2 : k < 2503) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2501 then cr_2500_2501 k h1 h else cr_2501_2503 k (by omega) h2
theorem cr_2497_2503 (k : ℕ) (h1 : 2497 ≤ k) (h2 : k < 2503) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2500 then cr_2497_2500 k h1 h else cr_2500_2503 k (by omega) h2
theorem cr_2492_2503 (k : ℕ) (h1 : 2492 ≤ k) (h2 : k < 2503) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2497 then cr_2492_2497 k h1 h else cr_2497_2503 k (by omega) h2
theorem cr_2482_2503 (k : ℕ) (h1 : 2482 ≤ k) (h2 : k < 2503) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2492 then cr_2482_2492 k h1 h else cr_2492_2503 k (by omega) h2
theorem cr_2462_2503 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2503) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2482 then cr_2462_2482 k h1 h else cr_2482_2503 k (by omega) h2
theorem cr_2503_2504 (k : ℕ) (h1 : 2503 ≤ k) (h2 : k < 2504) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2503 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2503_ok
theorem cr_2504_2505 (k : ℕ) (h1 : 2504 ≤ k) (h2 : k < 2505) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2504 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2504_ok
theorem cr_2503_2505 (k : ℕ) (h1 : 2503 ≤ k) (h2 : k < 2505) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2504 then cr_2503_2504 k h1 h else cr_2504_2505 k (by omega) h2
theorem cr_2505_2506 (k : ℕ) (h1 : 2505 ≤ k) (h2 : k < 2506) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2505 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2505_ok
theorem cr_2506_2507 (k : ℕ) (h1 : 2506 ≤ k) (h2 : k < 2507) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2506 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2506_ok
theorem cr_2507_2508 (k : ℕ) (h1 : 2507 ≤ k) (h2 : k < 2508) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2507 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2507_ok
theorem cr_2506_2508 (k : ℕ) (h1 : 2506 ≤ k) (h2 : k < 2508) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2507 then cr_2506_2507 k h1 h else cr_2507_2508 k (by omega) h2
theorem cr_2505_2508 (k : ℕ) (h1 : 2505 ≤ k) (h2 : k < 2508) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2506 then cr_2505_2506 k h1 h else cr_2506_2508 k (by omega) h2
theorem cr_2503_2508 (k : ℕ) (h1 : 2503 ≤ k) (h2 : k < 2508) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2505 then cr_2503_2505 k h1 h else cr_2505_2508 k (by omega) h2
theorem cr_2508_2509 (k : ℕ) (h1 : 2508 ≤ k) (h2 : k < 2509) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2508 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2508_ok
theorem cr_2509_2510 (k : ℕ) (h1 : 2509 ≤ k) (h2 : k < 2510) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2509 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2509_ok
theorem cr_2508_2510 (k : ℕ) (h1 : 2508 ≤ k) (h2 : k < 2510) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2509 then cr_2508_2509 k h1 h else cr_2509_2510 k (by omega) h2
theorem cr_2510_2511 (k : ℕ) (h1 : 2510 ≤ k) (h2 : k < 2511) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2510 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2510_ok
theorem cr_2511_2512 (k : ℕ) (h1 : 2511 ≤ k) (h2 : k < 2512) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2511 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2511_ok
theorem cr_2512_2513 (k : ℕ) (h1 : 2512 ≤ k) (h2 : k < 2513) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2512 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2512_ok
theorem cr_2511_2513 (k : ℕ) (h1 : 2511 ≤ k) (h2 : k < 2513) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2512 then cr_2511_2512 k h1 h else cr_2512_2513 k (by omega) h2
theorem cr_2510_2513 (k : ℕ) (h1 : 2510 ≤ k) (h2 : k < 2513) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2511 then cr_2510_2511 k h1 h else cr_2511_2513 k (by omega) h2
theorem cr_2508_2513 (k : ℕ) (h1 : 2508 ≤ k) (h2 : k < 2513) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2510 then cr_2508_2510 k h1 h else cr_2510_2513 k (by omega) h2
theorem cr_2503_2513 (k : ℕ) (h1 : 2503 ≤ k) (h2 : k < 2513) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2508 then cr_2503_2508 k h1 h else cr_2508_2513 k (by omega) h2
theorem cr_2513_2514 (k : ℕ) (h1 : 2513 ≤ k) (h2 : k < 2514) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2513 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2513_ok
theorem cr_2514_2515 (k : ℕ) (h1 : 2514 ≤ k) (h2 : k < 2515) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2514 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2514_ok
theorem cr_2513_2515 (k : ℕ) (h1 : 2513 ≤ k) (h2 : k < 2515) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2514 then cr_2513_2514 k h1 h else cr_2514_2515 k (by omega) h2
theorem cr_2515_2516 (k : ℕ) (h1 : 2515 ≤ k) (h2 : k < 2516) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2515 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2515_ok
theorem cr_2516_2517 (k : ℕ) (h1 : 2516 ≤ k) (h2 : k < 2517) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2516 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2516_ok
theorem cr_2517_2518 (k : ℕ) (h1 : 2517 ≤ k) (h2 : k < 2518) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2517 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2517_ok
theorem cr_2516_2518 (k : ℕ) (h1 : 2516 ≤ k) (h2 : k < 2518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2517 then cr_2516_2517 k h1 h else cr_2517_2518 k (by omega) h2
theorem cr_2515_2518 (k : ℕ) (h1 : 2515 ≤ k) (h2 : k < 2518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2516 then cr_2515_2516 k h1 h else cr_2516_2518 k (by omega) h2
theorem cr_2513_2518 (k : ℕ) (h1 : 2513 ≤ k) (h2 : k < 2518) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2515 then cr_2513_2515 k h1 h else cr_2515_2518 k (by omega) h2
theorem cr_2518_2519 (k : ℕ) (h1 : 2518 ≤ k) (h2 : k < 2519) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2518 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2518_ok
theorem cr_2519_2520 (k : ℕ) (h1 : 2519 ≤ k) (h2 : k < 2520) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2519 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2519_ok
theorem cr_2518_2520 (k : ℕ) (h1 : 2518 ≤ k) (h2 : k < 2520) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2519 then cr_2518_2519 k h1 h else cr_2519_2520 k (by omega) h2
theorem cr_2520_2521 (k : ℕ) (h1 : 2520 ≤ k) (h2 : k < 2521) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2520 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2520_ok
theorem cr_2521_2522 (k : ℕ) (h1 : 2521 ≤ k) (h2 : k < 2522) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2521 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2521_ok
theorem cr_2522_2523 (k : ℕ) (h1 : 2522 ≤ k) (h2 : k < 2523) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2522 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2522_ok
theorem cr_2521_2523 (k : ℕ) (h1 : 2521 ≤ k) (h2 : k < 2523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2522 then cr_2521_2522 k h1 h else cr_2522_2523 k (by omega) h2
theorem cr_2520_2523 (k : ℕ) (h1 : 2520 ≤ k) (h2 : k < 2523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2521 then cr_2520_2521 k h1 h else cr_2521_2523 k (by omega) h2
theorem cr_2518_2523 (k : ℕ) (h1 : 2518 ≤ k) (h2 : k < 2523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2520 then cr_2518_2520 k h1 h else cr_2520_2523 k (by omega) h2
theorem cr_2513_2523 (k : ℕ) (h1 : 2513 ≤ k) (h2 : k < 2523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2518 then cr_2513_2518 k h1 h else cr_2518_2523 k (by omega) h2
theorem cr_2503_2523 (k : ℕ) (h1 : 2503 ≤ k) (h2 : k < 2523) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2513 then cr_2503_2513 k h1 h else cr_2513_2523 k (by omega) h2
theorem cr_2523_2524 (k : ℕ) (h1 : 2523 ≤ k) (h2 : k < 2524) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2523 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2523_ok
theorem cr_2524_2525 (k : ℕ) (h1 : 2524 ≤ k) (h2 : k < 2525) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2524 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2524_ok
theorem cr_2523_2525 (k : ℕ) (h1 : 2523 ≤ k) (h2 : k < 2525) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2524 then cr_2523_2524 k h1 h else cr_2524_2525 k (by omega) h2
theorem cr_2525_2526 (k : ℕ) (h1 : 2525 ≤ k) (h2 : k < 2526) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2525 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2525_ok
theorem cr_2526_2527 (k : ℕ) (h1 : 2526 ≤ k) (h2 : k < 2527) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2526 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2526_ok
theorem cr_2527_2528 (k : ℕ) (h1 : 2527 ≤ k) (h2 : k < 2528) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2527 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2527_ok
theorem cr_2526_2528 (k : ℕ) (h1 : 2526 ≤ k) (h2 : k < 2528) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2527 then cr_2526_2527 k h1 h else cr_2527_2528 k (by omega) h2
theorem cr_2525_2528 (k : ℕ) (h1 : 2525 ≤ k) (h2 : k < 2528) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2526 then cr_2525_2526 k h1 h else cr_2526_2528 k (by omega) h2
theorem cr_2523_2528 (k : ℕ) (h1 : 2523 ≤ k) (h2 : k < 2528) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2525 then cr_2523_2525 k h1 h else cr_2525_2528 k (by omega) h2
theorem cr_2528_2529 (k : ℕ) (h1 : 2528 ≤ k) (h2 : k < 2529) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2528 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2528_ok
theorem cr_2529_2530 (k : ℕ) (h1 : 2529 ≤ k) (h2 : k < 2530) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2529 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2529_ok
theorem cr_2528_2530 (k : ℕ) (h1 : 2528 ≤ k) (h2 : k < 2530) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2529 then cr_2528_2529 k h1 h else cr_2529_2530 k (by omega) h2
theorem cr_2530_2531 (k : ℕ) (h1 : 2530 ≤ k) (h2 : k < 2531) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2530 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2530_ok
theorem cr_2531_2532 (k : ℕ) (h1 : 2531 ≤ k) (h2 : k < 2532) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2531 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2531_ok
theorem cr_2532_2533 (k : ℕ) (h1 : 2532 ≤ k) (h2 : k < 2533) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2532 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2532_ok
theorem cr_2531_2533 (k : ℕ) (h1 : 2531 ≤ k) (h2 : k < 2533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2532 then cr_2531_2532 k h1 h else cr_2532_2533 k (by omega) h2
theorem cr_2530_2533 (k : ℕ) (h1 : 2530 ≤ k) (h2 : k < 2533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2531 then cr_2530_2531 k h1 h else cr_2531_2533 k (by omega) h2
theorem cr_2528_2533 (k : ℕ) (h1 : 2528 ≤ k) (h2 : k < 2533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2530 then cr_2528_2530 k h1 h else cr_2530_2533 k (by omega) h2
theorem cr_2523_2533 (k : ℕ) (h1 : 2523 ≤ k) (h2 : k < 2533) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2528 then cr_2523_2528 k h1 h else cr_2528_2533 k (by omega) h2
theorem cr_2533_2534 (k : ℕ) (h1 : 2533 ≤ k) (h2 : k < 2534) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2533 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2533_ok
theorem cr_2534_2535 (k : ℕ) (h1 : 2534 ≤ k) (h2 : k < 2535) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2534 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2534_ok
theorem cr_2533_2535 (k : ℕ) (h1 : 2533 ≤ k) (h2 : k < 2535) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2534 then cr_2533_2534 k h1 h else cr_2534_2535 k (by omega) h2
theorem cr_2535_2536 (k : ℕ) (h1 : 2535 ≤ k) (h2 : k < 2536) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2535 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2535_ok
theorem cr_2536_2537 (k : ℕ) (h1 : 2536 ≤ k) (h2 : k < 2537) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2536 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2536_ok
theorem cr_2537_2538 (k : ℕ) (h1 : 2537 ≤ k) (h2 : k < 2538) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2537 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2537_ok
theorem cr_2536_2538 (k : ℕ) (h1 : 2536 ≤ k) (h2 : k < 2538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2537 then cr_2536_2537 k h1 h else cr_2537_2538 k (by omega) h2
theorem cr_2535_2538 (k : ℕ) (h1 : 2535 ≤ k) (h2 : k < 2538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2536 then cr_2535_2536 k h1 h else cr_2536_2538 k (by omega) h2
theorem cr_2533_2538 (k : ℕ) (h1 : 2533 ≤ k) (h2 : k < 2538) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2535 then cr_2533_2535 k h1 h else cr_2535_2538 k (by omega) h2
theorem cr_2538_2539 (k : ℕ) (h1 : 2538 ≤ k) (h2 : k < 2539) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2538 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2538_ok
theorem cr_2539_2540 (k : ℕ) (h1 : 2539 ≤ k) (h2 : k < 2540) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2539 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2539_ok
theorem cr_2540_2541 (k : ℕ) (h1 : 2540 ≤ k) (h2 : k < 2541) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2540 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2540_ok
theorem cr_2539_2541 (k : ℕ) (h1 : 2539 ≤ k) (h2 : k < 2541) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2540 then cr_2539_2540 k h1 h else cr_2540_2541 k (by omega) h2
theorem cr_2538_2541 (k : ℕ) (h1 : 2538 ≤ k) (h2 : k < 2541) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2539 then cr_2538_2539 k h1 h else cr_2539_2541 k (by omega) h2
theorem cr_2541_2542 (k : ℕ) (h1 : 2541 ≤ k) (h2 : k < 2542) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2541 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2541_ok
theorem cr_2542_2543 (k : ℕ) (h1 : 2542 ≤ k) (h2 : k < 2543) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2542 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2542_ok
theorem cr_2543_2544 (k : ℕ) (h1 : 2543 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2543 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2543_ok
theorem cr_2542_2544 (k : ℕ) (h1 : 2542 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2543 then cr_2542_2543 k h1 h else cr_2543_2544 k (by omega) h2
theorem cr_2541_2544 (k : ℕ) (h1 : 2541 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2542 then cr_2541_2542 k h1 h else cr_2542_2544 k (by omega) h2
theorem cr_2538_2544 (k : ℕ) (h1 : 2538 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2541 then cr_2538_2541 k h1 h else cr_2541_2544 k (by omega) h2
theorem cr_2533_2544 (k : ℕ) (h1 : 2533 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2538 then cr_2533_2538 k h1 h else cr_2538_2544 k (by omega) h2
theorem cr_2523_2544 (k : ℕ) (h1 : 2523 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2533 then cr_2523_2533 k h1 h else cr_2533_2544 k (by omega) h2
theorem cr_2503_2544 (k : ℕ) (h1 : 2503 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2523 then cr_2503_2523 k h1 h else cr_2523_2544 k (by omega) h2
theorem cr_2462_2544 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2544) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2503 then cr_2462_2503 k h1 h else cr_2503_2544 k (by omega) h2
theorem cr_2544_2545 (k : ℕ) (h1 : 2544 ≤ k) (h2 : k < 2545) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2544 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2544_ok
theorem cr_2545_2546 (k : ℕ) (h1 : 2545 ≤ k) (h2 : k < 2546) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2545 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2545_ok
theorem cr_2544_2546 (k : ℕ) (h1 : 2544 ≤ k) (h2 : k < 2546) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2545 then cr_2544_2545 k h1 h else cr_2545_2546 k (by omega) h2
theorem cr_2546_2547 (k : ℕ) (h1 : 2546 ≤ k) (h2 : k < 2547) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2546 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2546_ok
theorem cr_2547_2548 (k : ℕ) (h1 : 2547 ≤ k) (h2 : k < 2548) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2547 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2547_ok
theorem cr_2548_2549 (k : ℕ) (h1 : 2548 ≤ k) (h2 : k < 2549) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2548 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2548_ok
theorem cr_2547_2549 (k : ℕ) (h1 : 2547 ≤ k) (h2 : k < 2549) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2548 then cr_2547_2548 k h1 h else cr_2548_2549 k (by omega) h2
theorem cr_2546_2549 (k : ℕ) (h1 : 2546 ≤ k) (h2 : k < 2549) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2547 then cr_2546_2547 k h1 h else cr_2547_2549 k (by omega) h2
theorem cr_2544_2549 (k : ℕ) (h1 : 2544 ≤ k) (h2 : k < 2549) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2546 then cr_2544_2546 k h1 h else cr_2546_2549 k (by omega) h2
theorem cr_2549_2550 (k : ℕ) (h1 : 2549 ≤ k) (h2 : k < 2550) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2549 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2549_ok
theorem cr_2550_2551 (k : ℕ) (h1 : 2550 ≤ k) (h2 : k < 2551) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2550 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2550_ok
theorem cr_2549_2551 (k : ℕ) (h1 : 2549 ≤ k) (h2 : k < 2551) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2550 then cr_2549_2550 k h1 h else cr_2550_2551 k (by omega) h2
theorem cr_2551_2552 (k : ℕ) (h1 : 2551 ≤ k) (h2 : k < 2552) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2551 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2551_ok
theorem cr_2552_2553 (k : ℕ) (h1 : 2552 ≤ k) (h2 : k < 2553) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2552 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2552_ok
theorem cr_2553_2554 (k : ℕ) (h1 : 2553 ≤ k) (h2 : k < 2554) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2553 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2553_ok
theorem cr_2552_2554 (k : ℕ) (h1 : 2552 ≤ k) (h2 : k < 2554) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2553 then cr_2552_2553 k h1 h else cr_2553_2554 k (by omega) h2
theorem cr_2551_2554 (k : ℕ) (h1 : 2551 ≤ k) (h2 : k < 2554) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2552 then cr_2551_2552 k h1 h else cr_2552_2554 k (by omega) h2
theorem cr_2549_2554 (k : ℕ) (h1 : 2549 ≤ k) (h2 : k < 2554) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2551 then cr_2549_2551 k h1 h else cr_2551_2554 k (by omega) h2
theorem cr_2544_2554 (k : ℕ) (h1 : 2544 ≤ k) (h2 : k < 2554) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2549 then cr_2544_2549 k h1 h else cr_2549_2554 k (by omega) h2
theorem cr_2554_2555 (k : ℕ) (h1 : 2554 ≤ k) (h2 : k < 2555) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2554 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2554_ok
theorem cr_2555_2556 (k : ℕ) (h1 : 2555 ≤ k) (h2 : k < 2556) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2555 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2555_ok
theorem cr_2554_2556 (k : ℕ) (h1 : 2554 ≤ k) (h2 : k < 2556) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2555 then cr_2554_2555 k h1 h else cr_2555_2556 k (by omega) h2
theorem cr_2556_2557 (k : ℕ) (h1 : 2556 ≤ k) (h2 : k < 2557) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2556 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2556_ok
theorem cr_2557_2558 (k : ℕ) (h1 : 2557 ≤ k) (h2 : k < 2558) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2557 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2557_ok
theorem cr_2558_2559 (k : ℕ) (h1 : 2558 ≤ k) (h2 : k < 2559) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2558 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2558_ok
theorem cr_2557_2559 (k : ℕ) (h1 : 2557 ≤ k) (h2 : k < 2559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2558 then cr_2557_2558 k h1 h else cr_2558_2559 k (by omega) h2
theorem cr_2556_2559 (k : ℕ) (h1 : 2556 ≤ k) (h2 : k < 2559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2557 then cr_2556_2557 k h1 h else cr_2557_2559 k (by omega) h2
theorem cr_2554_2559 (k : ℕ) (h1 : 2554 ≤ k) (h2 : k < 2559) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2556 then cr_2554_2556 k h1 h else cr_2556_2559 k (by omega) h2
theorem cr_2559_2560 (k : ℕ) (h1 : 2559 ≤ k) (h2 : k < 2560) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2559 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2559_ok
theorem cr_2560_2561 (k : ℕ) (h1 : 2560 ≤ k) (h2 : k < 2561) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2560 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2560_ok
theorem cr_2559_2561 (k : ℕ) (h1 : 2559 ≤ k) (h2 : k < 2561) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2560 then cr_2559_2560 k h1 h else cr_2560_2561 k (by omega) h2
theorem cr_2561_2562 (k : ℕ) (h1 : 2561 ≤ k) (h2 : k < 2562) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2561 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2561_ok
theorem cr_2562_2563 (k : ℕ) (h1 : 2562 ≤ k) (h2 : k < 2563) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2562 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2562_ok
theorem cr_2563_2564 (k : ℕ) (h1 : 2563 ≤ k) (h2 : k < 2564) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2563 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2563_ok
theorem cr_2562_2564 (k : ℕ) (h1 : 2562 ≤ k) (h2 : k < 2564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2563 then cr_2562_2563 k h1 h else cr_2563_2564 k (by omega) h2
theorem cr_2561_2564 (k : ℕ) (h1 : 2561 ≤ k) (h2 : k < 2564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2562 then cr_2561_2562 k h1 h else cr_2562_2564 k (by omega) h2
theorem cr_2559_2564 (k : ℕ) (h1 : 2559 ≤ k) (h2 : k < 2564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2561 then cr_2559_2561 k h1 h else cr_2561_2564 k (by omega) h2
theorem cr_2554_2564 (k : ℕ) (h1 : 2554 ≤ k) (h2 : k < 2564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2559 then cr_2554_2559 k h1 h else cr_2559_2564 k (by omega) h2
theorem cr_2544_2564 (k : ℕ) (h1 : 2544 ≤ k) (h2 : k < 2564) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2554 then cr_2544_2554 k h1 h else cr_2554_2564 k (by omega) h2
theorem cr_2564_2565 (k : ℕ) (h1 : 2564 ≤ k) (h2 : k < 2565) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2564 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2564_ok
theorem cr_2565_2566 (k : ℕ) (h1 : 2565 ≤ k) (h2 : k < 2566) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2565 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2565_ok
theorem cr_2564_2566 (k : ℕ) (h1 : 2564 ≤ k) (h2 : k < 2566) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2565 then cr_2564_2565 k h1 h else cr_2565_2566 k (by omega) h2
theorem cr_2566_2567 (k : ℕ) (h1 : 2566 ≤ k) (h2 : k < 2567) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2566 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2566_ok
theorem cr_2567_2568 (k : ℕ) (h1 : 2567 ≤ k) (h2 : k < 2568) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2567 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2567_ok
theorem cr_2568_2569 (k : ℕ) (h1 : 2568 ≤ k) (h2 : k < 2569) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2568 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2568_ok
theorem cr_2567_2569 (k : ℕ) (h1 : 2567 ≤ k) (h2 : k < 2569) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2568 then cr_2567_2568 k h1 h else cr_2568_2569 k (by omega) h2
theorem cr_2566_2569 (k : ℕ) (h1 : 2566 ≤ k) (h2 : k < 2569) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2567 then cr_2566_2567 k h1 h else cr_2567_2569 k (by omega) h2
theorem cr_2564_2569 (k : ℕ) (h1 : 2564 ≤ k) (h2 : k < 2569) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2566 then cr_2564_2566 k h1 h else cr_2566_2569 k (by omega) h2
theorem cr_2569_2570 (k : ℕ) (h1 : 2569 ≤ k) (h2 : k < 2570) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2569 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2569_ok
theorem cr_2570_2571 (k : ℕ) (h1 : 2570 ≤ k) (h2 : k < 2571) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2570 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2570_ok
theorem cr_2569_2571 (k : ℕ) (h1 : 2569 ≤ k) (h2 : k < 2571) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2570 then cr_2569_2570 k h1 h else cr_2570_2571 k (by omega) h2
theorem cr_2571_2572 (k : ℕ) (h1 : 2571 ≤ k) (h2 : k < 2572) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2571 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2571_ok
theorem cr_2572_2573 (k : ℕ) (h1 : 2572 ≤ k) (h2 : k < 2573) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2572 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2572_ok
theorem cr_2573_2574 (k : ℕ) (h1 : 2573 ≤ k) (h2 : k < 2574) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2573 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2573_ok
theorem cr_2572_2574 (k : ℕ) (h1 : 2572 ≤ k) (h2 : k < 2574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2573 then cr_2572_2573 k h1 h else cr_2573_2574 k (by omega) h2
theorem cr_2571_2574 (k : ℕ) (h1 : 2571 ≤ k) (h2 : k < 2574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2572 then cr_2571_2572 k h1 h else cr_2572_2574 k (by omega) h2
theorem cr_2569_2574 (k : ℕ) (h1 : 2569 ≤ k) (h2 : k < 2574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2571 then cr_2569_2571 k h1 h else cr_2571_2574 k (by omega) h2
theorem cr_2564_2574 (k : ℕ) (h1 : 2564 ≤ k) (h2 : k < 2574) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2569 then cr_2564_2569 k h1 h else cr_2569_2574 k (by omega) h2
theorem cr_2574_2575 (k : ℕ) (h1 : 2574 ≤ k) (h2 : k < 2575) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2574 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2574_ok
theorem cr_2575_2576 (k : ℕ) (h1 : 2575 ≤ k) (h2 : k < 2576) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2575 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2575_ok
theorem cr_2574_2576 (k : ℕ) (h1 : 2574 ≤ k) (h2 : k < 2576) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2575 then cr_2574_2575 k h1 h else cr_2575_2576 k (by omega) h2
theorem cr_2576_2577 (k : ℕ) (h1 : 2576 ≤ k) (h2 : k < 2577) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2576 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2576_ok
theorem cr_2577_2578 (k : ℕ) (h1 : 2577 ≤ k) (h2 : k < 2578) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2577 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2577_ok
theorem cr_2578_2579 (k : ℕ) (h1 : 2578 ≤ k) (h2 : k < 2579) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2578 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2578_ok
theorem cr_2577_2579 (k : ℕ) (h1 : 2577 ≤ k) (h2 : k < 2579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2578 then cr_2577_2578 k h1 h else cr_2578_2579 k (by omega) h2
theorem cr_2576_2579 (k : ℕ) (h1 : 2576 ≤ k) (h2 : k < 2579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2577 then cr_2576_2577 k h1 h else cr_2577_2579 k (by omega) h2
theorem cr_2574_2579 (k : ℕ) (h1 : 2574 ≤ k) (h2 : k < 2579) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2576 then cr_2574_2576 k h1 h else cr_2576_2579 k (by omega) h2
theorem cr_2579_2580 (k : ℕ) (h1 : 2579 ≤ k) (h2 : k < 2580) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2579 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2579_ok
theorem cr_2580_2581 (k : ℕ) (h1 : 2580 ≤ k) (h2 : k < 2581) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2580 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2580_ok
theorem cr_2581_2582 (k : ℕ) (h1 : 2581 ≤ k) (h2 : k < 2582) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2581 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2581_ok
theorem cr_2580_2582 (k : ℕ) (h1 : 2580 ≤ k) (h2 : k < 2582) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2581 then cr_2580_2581 k h1 h else cr_2581_2582 k (by omega) h2
theorem cr_2579_2582 (k : ℕ) (h1 : 2579 ≤ k) (h2 : k < 2582) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2580 then cr_2579_2580 k h1 h else cr_2580_2582 k (by omega) h2
theorem cr_2582_2583 (k : ℕ) (h1 : 2582 ≤ k) (h2 : k < 2583) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2582 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2582_ok
theorem cr_2583_2584 (k : ℕ) (h1 : 2583 ≤ k) (h2 : k < 2584) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2583 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2583_ok
theorem cr_2584_2585 (k : ℕ) (h1 : 2584 ≤ k) (h2 : k < 2585) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2584 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2584_ok
theorem cr_2583_2585 (k : ℕ) (h1 : 2583 ≤ k) (h2 : k < 2585) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2584 then cr_2583_2584 k h1 h else cr_2584_2585 k (by omega) h2
theorem cr_2582_2585 (k : ℕ) (h1 : 2582 ≤ k) (h2 : k < 2585) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2583 then cr_2582_2583 k h1 h else cr_2583_2585 k (by omega) h2
theorem cr_2579_2585 (k : ℕ) (h1 : 2579 ≤ k) (h2 : k < 2585) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2582 then cr_2579_2582 k h1 h else cr_2582_2585 k (by omega) h2
theorem cr_2574_2585 (k : ℕ) (h1 : 2574 ≤ k) (h2 : k < 2585) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2579 then cr_2574_2579 k h1 h else cr_2579_2585 k (by omega) h2
theorem cr_2564_2585 (k : ℕ) (h1 : 2564 ≤ k) (h2 : k < 2585) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2574 then cr_2564_2574 k h1 h else cr_2574_2585 k (by omega) h2
theorem cr_2544_2585 (k : ℕ) (h1 : 2544 ≤ k) (h2 : k < 2585) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2564 then cr_2544_2564 k h1 h else cr_2564_2585 k (by omega) h2
theorem cr_2585_2586 (k : ℕ) (h1 : 2585 ≤ k) (h2 : k < 2586) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2585 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2585_ok
theorem cr_2586_2587 (k : ℕ) (h1 : 2586 ≤ k) (h2 : k < 2587) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2586 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2586_ok
theorem cr_2585_2587 (k : ℕ) (h1 : 2585 ≤ k) (h2 : k < 2587) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2586 then cr_2585_2586 k h1 h else cr_2586_2587 k (by omega) h2
theorem cr_2587_2588 (k : ℕ) (h1 : 2587 ≤ k) (h2 : k < 2588) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2587 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2587_ok
theorem cr_2588_2589 (k : ℕ) (h1 : 2588 ≤ k) (h2 : k < 2589) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2588 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2588_ok
theorem cr_2589_2590 (k : ℕ) (h1 : 2589 ≤ k) (h2 : k < 2590) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2589 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2589_ok
theorem cr_2588_2590 (k : ℕ) (h1 : 2588 ≤ k) (h2 : k < 2590) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2589 then cr_2588_2589 k h1 h else cr_2589_2590 k (by omega) h2
theorem cr_2587_2590 (k : ℕ) (h1 : 2587 ≤ k) (h2 : k < 2590) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2588 then cr_2587_2588 k h1 h else cr_2588_2590 k (by omega) h2
theorem cr_2585_2590 (k : ℕ) (h1 : 2585 ≤ k) (h2 : k < 2590) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2587 then cr_2585_2587 k h1 h else cr_2587_2590 k (by omega) h2
theorem cr_2590_2591 (k : ℕ) (h1 : 2590 ≤ k) (h2 : k < 2591) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2590 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2590_ok
theorem cr_2591_2592 (k : ℕ) (h1 : 2591 ≤ k) (h2 : k < 2592) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2591 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2591_ok
theorem cr_2590_2592 (k : ℕ) (h1 : 2590 ≤ k) (h2 : k < 2592) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2591 then cr_2590_2591 k h1 h else cr_2591_2592 k (by omega) h2
theorem cr_2592_2593 (k : ℕ) (h1 : 2592 ≤ k) (h2 : k < 2593) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2592 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2592_ok
theorem cr_2593_2594 (k : ℕ) (h1 : 2593 ≤ k) (h2 : k < 2594) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2593 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2593_ok
theorem cr_2594_2595 (k : ℕ) (h1 : 2594 ≤ k) (h2 : k < 2595) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2594 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2594_ok
theorem cr_2593_2595 (k : ℕ) (h1 : 2593 ≤ k) (h2 : k < 2595) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2594 then cr_2593_2594 k h1 h else cr_2594_2595 k (by omega) h2
theorem cr_2592_2595 (k : ℕ) (h1 : 2592 ≤ k) (h2 : k < 2595) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2593 then cr_2592_2593 k h1 h else cr_2593_2595 k (by omega) h2
theorem cr_2590_2595 (k : ℕ) (h1 : 2590 ≤ k) (h2 : k < 2595) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2592 then cr_2590_2592 k h1 h else cr_2592_2595 k (by omega) h2
theorem cr_2585_2595 (k : ℕ) (h1 : 2585 ≤ k) (h2 : k < 2595) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2590 then cr_2585_2590 k h1 h else cr_2590_2595 k (by omega) h2
theorem cr_2595_2596 (k : ℕ) (h1 : 2595 ≤ k) (h2 : k < 2596) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2595 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2595_ok
theorem cr_2596_2597 (k : ℕ) (h1 : 2596 ≤ k) (h2 : k < 2597) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2596 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2596_ok
theorem cr_2595_2597 (k : ℕ) (h1 : 2595 ≤ k) (h2 : k < 2597) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2596 then cr_2595_2596 k h1 h else cr_2596_2597 k (by omega) h2
theorem cr_2597_2598 (k : ℕ) (h1 : 2597 ≤ k) (h2 : k < 2598) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2597 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2597_ok
theorem cr_2598_2599 (k : ℕ) (h1 : 2598 ≤ k) (h2 : k < 2599) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2598 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2598_ok
theorem cr_2599_2600 (k : ℕ) (h1 : 2599 ≤ k) (h2 : k < 2600) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2599 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2599_ok
theorem cr_2598_2600 (k : ℕ) (h1 : 2598 ≤ k) (h2 : k < 2600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2599 then cr_2598_2599 k h1 h else cr_2599_2600 k (by omega) h2
theorem cr_2597_2600 (k : ℕ) (h1 : 2597 ≤ k) (h2 : k < 2600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2598 then cr_2597_2598 k h1 h else cr_2598_2600 k (by omega) h2
theorem cr_2595_2600 (k : ℕ) (h1 : 2595 ≤ k) (h2 : k < 2600) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2597 then cr_2595_2597 k h1 h else cr_2597_2600 k (by omega) h2
theorem cr_2600_2601 (k : ℕ) (h1 : 2600 ≤ k) (h2 : k < 2601) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2600 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2600_ok
theorem cr_2601_2602 (k : ℕ) (h1 : 2601 ≤ k) (h2 : k < 2602) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2601 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2601_ok
theorem cr_2602_2603 (k : ℕ) (h1 : 2602 ≤ k) (h2 : k < 2603) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2602 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2602_ok
theorem cr_2601_2603 (k : ℕ) (h1 : 2601 ≤ k) (h2 : k < 2603) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2602 then cr_2601_2602 k h1 h else cr_2602_2603 k (by omega) h2
theorem cr_2600_2603 (k : ℕ) (h1 : 2600 ≤ k) (h2 : k < 2603) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2601 then cr_2600_2601 k h1 h else cr_2601_2603 k (by omega) h2
theorem cr_2603_2604 (k : ℕ) (h1 : 2603 ≤ k) (h2 : k < 2604) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2603 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2603_ok
theorem cr_2604_2605 (k : ℕ) (h1 : 2604 ≤ k) (h2 : k < 2605) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2604 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2604_ok
theorem cr_2605_2606 (k : ℕ) (h1 : 2605 ≤ k) (h2 : k < 2606) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2605 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2605_ok
theorem cr_2604_2606 (k : ℕ) (h1 : 2604 ≤ k) (h2 : k < 2606) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2605 then cr_2604_2605 k h1 h else cr_2605_2606 k (by omega) h2
theorem cr_2603_2606 (k : ℕ) (h1 : 2603 ≤ k) (h2 : k < 2606) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2604 then cr_2603_2604 k h1 h else cr_2604_2606 k (by omega) h2
theorem cr_2600_2606 (k : ℕ) (h1 : 2600 ≤ k) (h2 : k < 2606) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2603 then cr_2600_2603 k h1 h else cr_2603_2606 k (by omega) h2
theorem cr_2595_2606 (k : ℕ) (h1 : 2595 ≤ k) (h2 : k < 2606) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2600 then cr_2595_2600 k h1 h else cr_2600_2606 k (by omega) h2
theorem cr_2585_2606 (k : ℕ) (h1 : 2585 ≤ k) (h2 : k < 2606) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2595 then cr_2585_2595 k h1 h else cr_2595_2606 k (by omega) h2
theorem cr_2606_2607 (k : ℕ) (h1 : 2606 ≤ k) (h2 : k < 2607) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2606 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2606_ok
theorem cr_2607_2608 (k : ℕ) (h1 : 2607 ≤ k) (h2 : k < 2608) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2607 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2607_ok
theorem cr_2606_2608 (k : ℕ) (h1 : 2606 ≤ k) (h2 : k < 2608) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2607 then cr_2606_2607 k h1 h else cr_2607_2608 k (by omega) h2
theorem cr_2608_2609 (k : ℕ) (h1 : 2608 ≤ k) (h2 : k < 2609) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2608 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2608_ok
theorem cr_2609_2610 (k : ℕ) (h1 : 2609 ≤ k) (h2 : k < 2610) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2609 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2609_ok
theorem cr_2610_2611 (k : ℕ) (h1 : 2610 ≤ k) (h2 : k < 2611) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2610 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2610_ok
theorem cr_2609_2611 (k : ℕ) (h1 : 2609 ≤ k) (h2 : k < 2611) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2610 then cr_2609_2610 k h1 h else cr_2610_2611 k (by omega) h2
theorem cr_2608_2611 (k : ℕ) (h1 : 2608 ≤ k) (h2 : k < 2611) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2609 then cr_2608_2609 k h1 h else cr_2609_2611 k (by omega) h2
theorem cr_2606_2611 (k : ℕ) (h1 : 2606 ≤ k) (h2 : k < 2611) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2608 then cr_2606_2608 k h1 h else cr_2608_2611 k (by omega) h2
theorem cr_2611_2612 (k : ℕ) (h1 : 2611 ≤ k) (h2 : k < 2612) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2611 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2611_ok
theorem cr_2612_2613 (k : ℕ) (h1 : 2612 ≤ k) (h2 : k < 2613) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2612 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2612_ok
theorem cr_2611_2613 (k : ℕ) (h1 : 2611 ≤ k) (h2 : k < 2613) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2612 then cr_2611_2612 k h1 h else cr_2612_2613 k (by omega) h2
theorem cr_2613_2614 (k : ℕ) (h1 : 2613 ≤ k) (h2 : k < 2614) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2613 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2613_ok
theorem cr_2614_2615 (k : ℕ) (h1 : 2614 ≤ k) (h2 : k < 2615) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2614 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2614_ok
theorem cr_2615_2616 (k : ℕ) (h1 : 2615 ≤ k) (h2 : k < 2616) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2615 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2615_ok
theorem cr_2614_2616 (k : ℕ) (h1 : 2614 ≤ k) (h2 : k < 2616) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2615 then cr_2614_2615 k h1 h else cr_2615_2616 k (by omega) h2
theorem cr_2613_2616 (k : ℕ) (h1 : 2613 ≤ k) (h2 : k < 2616) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2614 then cr_2613_2614 k h1 h else cr_2614_2616 k (by omega) h2
theorem cr_2611_2616 (k : ℕ) (h1 : 2611 ≤ k) (h2 : k < 2616) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2613 then cr_2611_2613 k h1 h else cr_2613_2616 k (by omega) h2
theorem cr_2606_2616 (k : ℕ) (h1 : 2606 ≤ k) (h2 : k < 2616) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2611 then cr_2606_2611 k h1 h else cr_2611_2616 k (by omega) h2
theorem cr_2616_2617 (k : ℕ) (h1 : 2616 ≤ k) (h2 : k < 2617) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2616 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2616_ok
theorem cr_2617_2618 (k : ℕ) (h1 : 2617 ≤ k) (h2 : k < 2618) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2617 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2617_ok
theorem cr_2616_2618 (k : ℕ) (h1 : 2616 ≤ k) (h2 : k < 2618) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2617 then cr_2616_2617 k h1 h else cr_2617_2618 k (by omega) h2
theorem cr_2618_2619 (k : ℕ) (h1 : 2618 ≤ k) (h2 : k < 2619) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2618 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2618_ok
theorem cr_2619_2620 (k : ℕ) (h1 : 2619 ≤ k) (h2 : k < 2620) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2619 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2619_ok
theorem cr_2620_2621 (k : ℕ) (h1 : 2620 ≤ k) (h2 : k < 2621) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2620 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2620_ok
theorem cr_2619_2621 (k : ℕ) (h1 : 2619 ≤ k) (h2 : k < 2621) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2620 then cr_2619_2620 k h1 h else cr_2620_2621 k (by omega) h2
theorem cr_2618_2621 (k : ℕ) (h1 : 2618 ≤ k) (h2 : k < 2621) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2619 then cr_2618_2619 k h1 h else cr_2619_2621 k (by omega) h2
theorem cr_2616_2621 (k : ℕ) (h1 : 2616 ≤ k) (h2 : k < 2621) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2618 then cr_2616_2618 k h1 h else cr_2618_2621 k (by omega) h2
theorem cr_2621_2622 (k : ℕ) (h1 : 2621 ≤ k) (h2 : k < 2622) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2621 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2621_ok
theorem cr_2622_2623 (k : ℕ) (h1 : 2622 ≤ k) (h2 : k < 2623) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2622 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2622_ok
theorem cr_2623_2624 (k : ℕ) (h1 : 2623 ≤ k) (h2 : k < 2624) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2623 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2623_ok
theorem cr_2622_2624 (k : ℕ) (h1 : 2622 ≤ k) (h2 : k < 2624) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2623 then cr_2622_2623 k h1 h else cr_2623_2624 k (by omega) h2
theorem cr_2621_2624 (k : ℕ) (h1 : 2621 ≤ k) (h2 : k < 2624) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2622 then cr_2621_2622 k h1 h else cr_2622_2624 k (by omega) h2
theorem cr_2624_2625 (k : ℕ) (h1 : 2624 ≤ k) (h2 : k < 2625) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2624 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2624_ok
theorem cr_2625_2626 (k : ℕ) (h1 : 2625 ≤ k) (h2 : k < 2626) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2625 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2625_ok
theorem cr_2626_2627 (k : ℕ) (h1 : 2626 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 := by
  obtain rfl : k = 2626 := by omega
  exact ALeaf.check_sound tables tables_valid _ _ _ leaf2626_ok
theorem cr_2625_2627 (k : ℕ) (h1 : 2625 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2626 then cr_2625_2626 k h1 h else cr_2626_2627 k (by omega) h2
theorem cr_2624_2627 (k : ℕ) (h1 : 2624 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2625 then cr_2624_2625 k h1 h else cr_2625_2627 k (by omega) h2
theorem cr_2621_2627 (k : ℕ) (h1 : 2621 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2624 then cr_2621_2624 k h1 h else cr_2624_2627 k (by omega) h2
theorem cr_2616_2627 (k : ℕ) (h1 : 2616 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2621 then cr_2616_2621 k h1 h else cr_2621_2627 k (by omega) h2
theorem cr_2606_2627 (k : ℕ) (h1 : 2606 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2616 then cr_2606_2616 k h1 h else cr_2616_2627 k (by omega) h2
theorem cr_2585_2627 (k : ℕ) (h1 : 2585 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2606 then cr_2585_2606 k h1 h else cr_2606_2627 k (by omega) h2
theorem cr_2544_2627 (k : ℕ) (h1 : 2544 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2585 then cr_2544_2585 k h1 h else cr_2585_2627 k (by omega) h2
theorem cr_2462_2627 (k : ℕ) (h1 : 2462 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2544 then cr_2462_2544 k h1 h else cr_2544_2627 k (by omega) h2
theorem cr_2298_2627 (k : ℕ) (h1 : 2298 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2462 then cr_2298_2462 k h1 h else cr_2462_2627 k (by omega) h2
theorem cr_1970_2627 (k : ℕ) (h1 : 1970 ≤ k) (h2 : k < 2627) : Covered (boxes k).1 (boxes k).2 :=
  if h : k < 2298 then cr_1970_2298 k h1 h else cr_2298_2627 k (by omega) h2

end Harris
