#
#MIT License
#
#Copyright (c) 2020 NEOS-Server
#
#Permission is hereby granted, free of charge, to any person obtaining a copy
#of this software and associated documentation files (the "Software"), to deal
#in the Software without restriction, including without limitation the rights
#to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#copies of the Software, and to permit persons to whom the Software is
#furnished to do so, subject to the following conditions:
#
#The above copyright notice and this permission notice shall be included in all
#copies or substantial portions of the Software.
#
#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
#OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
#SOFTWARE.
#

import os
import linecache
try:
  import zipextimporter
except:
  pass
import re
import xmlrpc.client
import sys
import time
import socket
import base64
import gzip
import io
import xml.dom.minidom
import string
import pathlib
import ssl
import certifi

solverMap = {}
solverMap[ 1] = 'cbc'    # lp
solverMap[ 2] = 'cbc'    # mip
solverMap[ 3] = 'cbc'    # rmip
solverMap[ 4] = 'ipopt'  # nlp
solverMap[ 5] = 'path'   # mcp
solverMap[ 6] = 'nlpec'  # mpec
solverMap[ 7] = 'nlpec'  # rmpec
solverMap[ 8] = 'path'   # cns
solverMap[ 9] = 'ipopt'  # dnlp
solverMap[10] = 'ipopt'  # rminlp
solverMap[11] = 'shot'   # minlp
solverMap[12] = 'ipopt'  # qcp
solverMap[13] = 'shot'   # miqcp
solverMap[14] = 'ipopt'  # rmiqcp
solverMap[15] = 'jams'   # emp

class KestrelException(Exception):
  def __init__(self,msg):
    Exception.__init__(self)
    self.msg = msg

  def __str__(self):
    return repr(self.msg)

class KestrelSolverException(KestrelException):
  def __init__(self,msg,solverlist):
    KestrelException.__init__(self,msg)
    self.msg += "\nCreate options file and include the following lines:\n\tkestrel_solver <solvername>\n"
    self.msg += "\tneos_server <hostname>[:<port>]\n\n"
    self.msg += "The following solvers are available on NEOS:\n"
    for solver in solverlist:
      self.msg += solver.upper() +"\n"

class KestrelGamsClient:
  def __init__(self,argv):
    self.argv=argv
    self.serverProtocol="https"
    self.serverHost="neos-server.org"
    self.serverPort=3333
    self.solverName=None
    self.jobNumber=None
    self.password=None
    self.priority="long"
    self.socket_timeout=0
    self.authUsername=None
    self.authUserPassword=None

    # action-parameter is outdated
    '''
    if len(self.argv) >= 3:
      self.cntrfile = self.argv[2]
      self.action = self.argv[1].lower()
      if self.action not in ['kill','retrieve','submit','solve']:
        self.Usage()
    else:
      self.Usage()
     '''

    if len(self.argv) >= 2:
      self.cntrfile = self.argv[1]
      self.action = 'solve'
    else:
      self.Usage()

  def Usage(self):
    sys.stderr.write("\n--- Kestrel fatal error: usage\n")
    sys.stderr.write("  gamske_ux.out <cntrfile>\n")
    sys.exit(1)

  def Fatal(self, str):
    sys.stderr.write("\n--- Kestrel fatal error: %s\n\n" % str)
    sys.exit(1)

  def Error(self, str):
    if self.logopt in [1,3,4]:
      # Write the message to standard output
      sys.stdout.write("\n--- Kestrel error: %s\n\n" % str)

    if self.logopt in [2,4]:
      # Append the error message to the logfile indicated
      try:
        f = open(self.logfilename,'a')
        f.write("\n--- Kestrel error: %s\n\n" % str)
        f.close()
      except IOError as e:
        self.Fatal("Could not append to log file %s" % self.logfilename)

    try:
      f = open(self.statfilename,'a')
      f.write("=1\n\n--- Kestrel error: %s\n\n=2\n" % str)
      f.close()
    except IOError as e:
      self.Fatal("Could not append to status file %s\n" % self.statfilename)

    sys.exit(0)

  def getDefaultEmail(self):
    if 'NEOS_EMAIL' in os.environ:
      return os.environ['NEOS_EMAIL']
    return None

  def parseControlFile(self):
    """
    This function does the following with the cntr file
    line 13:
      extract isAscii, useOptions

    line 18:
      matrix file, save and change to gamsmatr.scr

    line 19:
      instruction file; save and change to gamsinst.scr

    line 20:
      set options file to 'kestrel.opt'

    line 21:
      status file; save and change to gamsstat.scr

    line 22:
      solution file; save and change to gamssolu.scr

    line 23:
      log file; save and remove absolute path

    line 24:
      dictionary file; save and change to gamsdict.scr

    line 25:
      set to '2' to write to log file

    line 28-30:
      set working,system,scratch directories to '.'

    line 33,34,35:
      remove license

    line 37:
      set parameter file

    line 38:
      read #models #solvers
      ignore next #models + 2*#solvers with (SOLVER # # 0 ..) +
                 3*#solvers with (SOLVER # # 1 ...)   lines

    next two lines are more license (remove them)

    set directories of remaining paths to current directory
     (.scr, .so, sbbinfo.)

    change the scratch file extension to 'scr'
    """

    try:
      f = open(self.cntrfile,'r')
      lines = f.readlines()
      f.close()
    except IOError as e:
      self.Fatal("Could not open control file %s" % self.cntrfile)

    # extract control version number
    self.cntver = 0
    m = re.match(r'(\d+)',lines[0])
    if m and m.groups():
      self.cntver = int(m.groups()[0])

    self.modeltype = int(lines[1].split()[0])

    if self.cntver not in [42, 44, 46, 47, 48, 49, 50, 51, 52, 53]:
      self.Fatal("GAMS cntr-file version 42, 44, 46, 47, 48, 49, 50, 51, 52, 53 required")

    # extract isAscii, useOptions
    m = re.match(r'(\d+)\s+(\d+)',lines[12])
    if m and m.groups():
      self.isAscii=m.groups()[0]
      self.useOptions = int(m.groups()[1])
    else:
      self.Fatal("Line 13 of the control file is incorrect")

    # is this is an MPSGE model?
    self.isMPSGE = int(lines[15].split()[0])

    # get the matrix and instruction scratch files and patch
    self.matrfilename = lines[17].strip()
    lines[17] = "gamsmatr.scr\n"

    self.instfilename = lines[18].strip()
    lines[18] = "gamsinst.scr\n"

    # patch option file name; always use kestrel.opt
    self.optfilename = ""
    m = re.match(r'(.*)kestrel.*\.(.*)',lines[19])
    if m and m.groups():
      self.optfilename = m.groups()[0] + "kestrel." + m.groups()[1]
    lines[19] = "kestrel.opt\n"

    # get the status and solution scratch files and patch
    self.statfilename = lines[20].strip()
    lines[20] = "gamsstat.scr\n"

    self.solufilename = lines[21].strip()
    lines[21] = "gamssolu.scr\n"

    # get the log filename and patch
    self.logfilename = lines[22].strip()
    lines[22] = "gamslog.scr\n"

    # get the dictionary filename and patch
    self.dictfilename = lines[23].strip()
    lines[23] = "gamsdict.scr\n"

    # get the logfile option, then make output written to logfile
    m = re.match(r'(\d+)',lines[24])
    if m and m.groups():
      self.logopt = int(m.groups()[0])
    lines[24]="2\n"

    # set working, system, and scratch directories
    self.scrdir = lines[29].strip()
    lines[27] = lines[28] = lines[29] = '.\n'

    # remove first part of license
    lines[32] = lines[33] = lines[34] = "\n"

    # patch parameter file
    lines[36] = "gmsprmun.scr"

    # downgrade the cntr-file version 53 to 52
    if self.cntver == 53:
      lines[0] = "52\n"
      # remove seventh and eigth license line, license gets replaced anyway
      del lines[-18]
      del lines[-18]
      self.cntver = 52

    # downgrade the cntr-file version 52 to 51
    if self.cntver == 52:
      # We do not yet handle models with more than INT_MAX NNZ in Kestrel
      lines[0] = "51\n"
      # remove final line of CF (u+15, rvec[ 28] rvec[ 29]
      lines = lines[:-1]
      self.cntver = 51

    # downgrade the cntr-file version 51 to 50
    if self.cntver == 51:
      # remove last number (savepoint) of this line
      lines[13] = lines[13].rpartition(' ')[0] + "\n"
      # 51 -> 50
      lines[0] = "50\n"
      self.cntver = 50

    # downgrade the cntr-file version 50 to 49 // No change required since this was in the license section which does not get copied
    if self.cntver == 50:
      # 50 -> 49
      lines[0] = "49\n"
      self.cntver = 49

    # downgrade the cntr-file version 49 to 48 // No change required since this was in the license section which does not get copied
    if self.cntver == 49:
      # 49 -> 48
      lines[0] = "48\n"
      self.cntver = 48

    # downgrade the cntr-file version 48 to 47
    if self.cntver == 48:
      # 48 -> 47
      lines[0] = "47\n"
      self.cntver = 47
      # remove last two numbers of this line
      lines[13] = lines[13].rpartition(' ')[0] + "\n"
      lines[13] = lines[13].rpartition(' ')[0] + "\n"

    # downgrade the cntr-file version 47 to 46
    if self.cntver == 47:
      # 47 -> 46
      lines[0] = "46\n"
      self.cntver = 46
    # remove line with file name
      lines = lines[:-2]
      lines.append("")

    # downgrade the cntr-file version 46 to 42
    # no support for threads, external funclib and guss
    if self.cntver == 46:
      # 46 -> 42
      lines[0] = "42\n"

      # remove last number of this line
      lines[2] = lines[2].rpartition(' ')[0] + "\n"

      # remove threads-option
      lines[13] = lines[13].rpartition(' ')[0] + "\n"

      # remove last two lines
      lines = lines[:-2]

      # treat the cntr-file now like a version 42 one
      self.cntver = 42

    # downgrade the cntr-file version 44 to 42
    elif self.cntver == 44:
      # 44 -> 42
      lines[0] = "42\n"

      # remove threads-option
      lines[13] = lines[13].rpartition(' ')[0] + "\n"

      # remove last line
      lines = lines[:-1]

      # treat the cntr-file now like a version 42 one
      self.cntver = 42

    if self.cntver == 42:
      # remove second part of license
      lines[-13] = lines[-12] = "\n"

      # make everything in local directory
      lines[-11] = 'model.scr\n'
      lines[-6] = 'model.so\n'
      lines[-5] = 'sbbinfo.scr\n'
      lines[-4] = 'gamscntr.scr\n'
      lines[-3] = './\n'

      # patch scratch file extension
      self.scrext = lines[-2].strip()
      lines[-2] = 'scr\n'

      # get the entire control file name
      self.cntr =  "".join(lines[:37]) + "".join(lines[-13:])

  def writeErrorOutputFiles(self):
    """
    This writes solution and status files returned when an error occurs.
    """

    try:
      f = open(self.statfilename,"w")
      f.write("""=0 Kestrel\n""")
      f.close()
    except IOError as e:
      self.Error("Could not initialize status file %s\n" % self.statfilename)

    try:
      f = open(self.solufilename,"w")
      f.write("""  1 6.0000000000000000E+00
  2 1.3000000000000000E+01
  3 0.0000000000000000E+00
  4 0.0
  5 0.0000000000000000E+00
  6 0.0
  7 0.0
  8 0.0
  0 0.0\n""")
      f.close()

    except IOError as e:
      self.Error("Could not open solution file %s\n" % self.solufilename)

  def writeLog(self, text):
    if self.logopt in [1,3,4]:
      sys.stdout.write(text)
    if self.logopt in [2,4]:
      try:
        f = open(self.logfilename,'a')
        f.write(text)
        f.close()
      except IOError as e:
        self.Fatal("Could not append to log file %s" % self.logfilename)

  def parseOptionsFile(self):
    if (self.useOptions == 0):
#      raise KestrelSolverException("No options file indicated\n",self.kestrelGamsSolvers)
      self.solverName = solverMap[self.modeltype]
    elif os.access(self.optfilename,os.R_OK):
      optfile = open(self.optfilename,'r')
      self.writeLog("Reading parameter(s) from \"" + self.optfilename + "\"\n")
      for line in optfile:
        m = re.match(r'neos_user_password[\s=]+(\S+)',line)
        if m:
          self.writeLog(">>  neos_user_password ******")
        else:
          self.writeLog(">>  " + line)

        m = re.match(r'kestrel_priority[\s=]+(\S+)',line)
        if m:
          value = m.groups()[0]
          if value.lower()=="short":
            self.priority = "short"

        m = re.match(r'kestrel_solver[\s=]+(\S+)',line)
        if m:
          self.solverName = m.groups()[0]

        m = re.match(r'neos_server[\s=]+(\S+)://(\S+):(\d+)',line)
        if m:
          self.serverProtocol = m.groups()[0]
          self.serverHost = m.groups()[1]
          self.serverPort = m.groups()[2]

        m = re.match(r'neos_username[\s=]+(\S+)',line)
        if m:
          self.authUsername = m.groups()[0]

        m = re.match(r'neos_user_password[\s=]+(\S+)',line)
        if m:
          self.authUserPassword = m.groups()[0]

        elif re.match(r'neos_server[\s=]+(\S+)://(\S+)',line):
          m = re.match(r'neos_server[\s=]+(\S+)://(\S+)',line)
          self.serverProtocol = m.groups()[0]
          self.serverHost = m.groups()[1]

        elif re.match(r'neos_server[\s=]+(\S+):(\d+)',line):
          m = re.match(r'neos_server[\s=]+(\S+):(\d+)',line)
          self.serverHost = m.groups()[0]
          self.serverPort = m.groups()[1]

        else:
          m = re.match(r'neos_server[\s=]+(\S+)',line)
          if m:
            self.serverHost = m.groups()[0]

        m = re.match(r'kestrel_(job|jobnumber|jobNumber)[\s=]+(\d+)', line)
        if m:
          self.jobNumber=int(m.groups()[1])

        m = re.match(r'kestrel_(pass|password)[\s=]+(\S+)', line)
        if m:
          self.password = m.groups()[1]

        m = re.match(r'socket_timeout[\s=]+(\d+)',line)
        if m:
          self.socket_timeout = m.groups()[0]
          socket.setdefaulttimeout(float(self.socket_timeout))

      optfile.close()
      self.writeLog("\nFinished reading from \"" + self.optfilename + "\"\n")
    else:
      raise KestrelSolverException("Could not read options file %s\n" % self.optfilename,self.kestrelGamsSolvers)

  def connectServer(self):
    if self.logopt in [1,3,4]:
      sys.stdout.write("Connecting to: %s://%s:%s\n" % (self.serverProtocol,self.serverHost,self.serverPort))
    if self.logopt in [2,4]:
      # Append the message to the logfile indicated
      try:
        f = open(kestrel.logfilename,'a')
        f.write("Connecting to: %s://%s:%s\n" % (self.serverProtocol,self.serverHost,self.serverPort))
        f.close()
      except IOError as e:
        self.Fatal("Could not append to log file %s" % self.logfilename)
    ssl_context = ssl.create_default_context()
    if ssl_context.minimum_version < ssl.TLSVersion.TLSv1_2:
        ssl_context.minimum_version = ssl.TLSVersion.TLSv1_2
    if sys.platform == "win32":
      ssl_context.load_verify_locations(certifi.where())
    self.neos = xmlrpc.client.Server("%s://%s:%s" % (self.serverProtocol,self.serverHost,self.serverPort), context=ssl_context)

    reply = self.neos.ping()
    if reply.find('alive') < 0:
      raise KestrelException("Unable to contact NEOS at https://%s:%d" % \
            (self.host, self.port))

  def obtainSolvers(self):
    # Form a list of all kestrel-gams solver available on NEOS
    allKestrelSolvers = self.neos.listSolversInCategory("kestrel")
    self.kestrelGamsSolvers = []
    for s in allKestrelSolvers:
      i = s.find(':GAMS')
      if i > 0:
        self.kestrelGamsSolvers.append(s[0:i])

  def checkOptionsFile(self):
    if self.solverName and (self.solverName.lower() not in [s.lower() for s in self.kestrelGamsSolvers]):
      errmsg = "Solver '%s' not available on NEOS.\n" % self.solverName
      raise KestrelSolverException(errmsg, self.kestrelGamsSolvers)

  def formSubmission(self):
    if not self.solverName:
      raise KestrelSolverException("No 'kestrel_solver' option found in option file\n",self.kestrelGamsSolvers)

    # Get the matrix, dictionary and instruction file
    gamsFiles = {}
    gamsFiles['cntr'] = io.BytesIO(self.cntr.encode())

    # Need to read empinfo.dat or empinfo.scr
    empInfoFileName = os.path.join(self.scrdir, "empinfo." + self.scrext)
    if os.access(empInfoFileName,os.R_OK):
      gamsFiles['empinfo'] = io.BytesIO()
      f = open(empInfoFileName,"rb")
      zipper = gzip.GzipFile(mode='wb',fileobj=gamsFiles['empinfo'])
      zipper.write(f.read())
      zipper.close()
      f.close()

    # Need to read scenarios
    scenDictName = os.path.join(self.scrdir, "scenario_dict." + self.scrext)
    if os.access(scenDictName,os.R_OK):
      gamsFiles['scenario'] = io.BytesIO()
      f = open(scenDictName,"rb")
      zipper = gzip.GzipFile(mode='wb',fileobj=gamsFiles['scenario'])
      zipper.write(f.read())
      zipper.close()
      f.close()

    if os.access(self.matrfilename,os.R_OK):
      gamsFiles['matr'] = io.BytesIO()
      f = open(self.matrfilename,"rb")
      zipper = gzip.GzipFile(mode='wb',fileobj=gamsFiles['matr'])
      zipper.write(f.read())
      zipper.close()
      f.close()

    if os.access(self.instfilename,os.R_OK):
      gamsFiles['inst'] = io.BytesIO()
      f = open(self.instfilename,"rb")
      zipper = gzip.GzipFile(mode='wb',fileobj=gamsFiles['inst'])
      zipper.write(f.read())
      zipper.close()
      f.close()

    if os.access(self.dictfilename,os.R_OK):
      gamsFiles['dict'] = io.BytesIO()
      f = open(self.dictfilename,"rb")
      zipper = gzip.GzipFile(mode='wb',fileobj=gamsFiles['dict'])
      zipper.write(f.read())
      zipper.close()
      f.close()

    if self.isMPSGE != 0 and self.modeltype == 5 and os.access(os.path.join(self.scrdir,'gedata.' + self.scrext),os.R_OK): # MCP might be an MPSGE model
      gamsFiles['cge'] = io.BytesIO()
      f = open(os.path.join(self.scrdir,'gedata.' + self.scrext),"rb")
      zipper = gzip.GzipFile(mode='wb',fileobj=gamsFiles['cge'])
      s=f.read()
      end = s.find(b"gamsdict.")
      if end != -1:
        start = end
        while ord(s[end]) != 32: #whitespace
          end = end+1
        while ord(s[start]) != 0:
          start = start-1
        orgStr = s[start+1:end]
        replStr = b"./gamsdict.scr" + b" "*(len(orgStr) - len("./gamsdict.scr"))
        s = s.replace(orgStr, replStr)
      zipper.write(s)
      zipper.close()
      f.close()

    self.xml = """
      <document>
      <category>kestrel</category>
      <solver>%s</solver>
      <inputType>GAMS</inputType>
      <priority>%s</priority>
      """ % (self.solverName,self.priority)

    for key in list(gamsFiles.keys()):
      self.xml += "<%s><base64>%s</base64></%s>\n" % (key,base64.b64encode(gamsFiles[key].getvalue()).decode(),key)
      gamsFiles[key].close()

    # Remove 'kestrel', 'neos' and 'socket_timeout' options from options file; they are not needed
    email = None
    xpressemail = None
    runningtime = None
    self.xml += "<options><![CDATA["
    if self.useOptions:
      with open(self.optfilename) as fp:
        for line in fp.readlines():
          if not re.match(r'kestrel|neos_server|neos_username|neos_user_password|email|xpressemail|runtime|socket_timeout',line):
            self.xml += line
          elif re.match(r'email',line):
            email = line.rsplit()[1]
          elif re.match(r'xpressemail',line):
            xpressemail = line.rsplit()[1]
          elif re.match(r'runtime',line):
            runningtime = line.rsplit()[1]
    self.xml += "]]></options>\n"

    if not email:
      email = self.getDefaultEmail()
    if not email:
      self.Error("No email address provided. Either specify it in an option file or set environment variable NEOS_EMAIL (e.g. via gamsconfig.yaml).")
    self.xml += "<email>"
    self.xml += email
    self.xml += "</email>\n"

    if xpressemail:
      self.xml += "<xpressemail>"
      self.xml += xpressemail
      self.xml += "</xpressemail>\n"

    if runningtime:
      self.xml += "<priority>"
      self.xml += runningtime
      self.xml += "</priority>"

    self.xml += "</document>"

  def submit(self):
    user = "%s on %s" % (os.getenv('LOGNAME'),
                         socket.getfqdn(socket.gethostname()))
    if self.authUsername is None or self.authUserPassword is None:
      if self.authUsername: self.writeLog("\nWarning: 'neos_username' was specified, but not 'neos_user_password'")
      if self.authUserPassword: self.writeLog("\nWarning: 'neos_user_password' was specified, but not 'neos_username'")
      (self.jobNumber,self.password) = \
                       self.neos.submitJob(self.xml,user,"kestrel")
    else:
      (self.jobNumber,self.password) = \
                       self.neos.authenticatedSubmitJob(self.xml,self.authUsername,self.authUserPassword,"kestrel")
    if self.jobNumber==0:
      raise KestrelException(self.password)

    if self.logopt in [1,3,4]:
      # Send the output to the screen
      sys.stdout.write("\nNEOS job#=%d, pass=%s\n\n" % (self.jobNumber,self.password))
      sys.stdout.write("Check the following URL for progress report :\n")
      #sys.stdout.write("http://www-neos.mcs.anl.gov/cgi-bin/nph-neos-solver.cgi?admin=results&jobnumber=%d&pass=%s\n\n" % (self.jobNumber,self.password))
      sys.stdout.write("%s://%s/neos/cgi-bin/nph-neos-solver.cgi?admin=results&jobnumber=%d&pass=%s\n\n" % (self.serverProtocol,self.serverHost,self.jobNumber,self.password))
    if self.logopt in [2,4]:
      # Append the error message to the logfile indicated
      try:
        f = open(self.logfilename,'a')
        f.write("\nNEOS job#=%d, pass=%s\n\n" % (self.jobNumber,self.password))
        f.write("Check the following URL for progress report :\n")
        f.write("%s://%s/neos/cgi-bin/nph-neos-solver.cgi?admin=results&jobnumber=%d&pass=%s\n\n" % (self.serverProtocol,self.serverHost,self.jobNumber,self.password))
        f.close()
      except IOError as e:
        self.Error("Could not append to log file %s" % self.logfilename)

    try:
      f = open(self.statfilename,'a')
      f.write("=1\n\n")
      f.write("\nNEOS job#=%d, pass=%s\n\n" % (self.jobNumber,self.password))
      f.write("Check the following URL for progress report :\n")
      f.write("%s://%s/neos/cgi-bin/nph-neos-solver.cgi?admin=results&jobnumber=%d&pass=%s\n\n" % (self.serverProtocol,self.serverHost,self.jobNumber,self.password))
      f.write("=2\n")
      f.close()
    except IOError as e:
      self.Error("Could not append to status file %s\n" % self.statfilename)

  def getText(self,node):
    """
    Returns the text from the node of an xml document
    """
    s = ""
    if isinstance(node,str):
      return node
    if isinstance(node.nodeValue,str):
      return node.data
    elif node.hasChildNodes():
      for n in node.childNodes:
        s += self.getText(n)
    return s

  def parseSolution(self,xmlstring):
    doc = xml.dom.minidom.parseString(xmlstring)
    for tag in ['allsolutions', 'scenrep']:
        xmltag = tag[:4]
        node = doc.getElementsByTagName(xmltag)
        if node and len(node):
          try:
            f = open(os.path.join(self.scrdir, f"{tag}.{self.scrext}"), 'wb')
            f.write(bytes.fromhex(self.getText(node[0])))
            f.close()
          except IOError as e:
            self.Error("Could not write file %s.%s\n" % (tag, self.scrext))
    node = doc.getElementsByTagName('solu')
    if node and len(node):
      try:
        f = open(self.solufilename,'w')
        f.write(self.getText(node[0]))
        f.close()
      except IOError as e:
        self.Error("Could not write solution file %s\n" % self.solufilename)

    node = doc.getElementsByTagName('stat')
    if node and len(node):
      try:
        f = open(self.statfilename,'w',errors='replace')
        f.write(self.getText(node[0]))
        f.close()
      except IOError as e:
        self.Error("Could not write status file %s\n" % self.statfilename)

    node = doc.getElementsByTagName('log')
    if node and len(node):
      if self.logopt in [1,3,4]:
        # Send the output to the screen
        encoding = sys.stdout.encoding
        encoded_text = self.getText(node[0]).encode(encoding,errors='replace').decode(encoding)
        sys.stdout.write(encoded_text)
      if self.logopt in [2,4]:
        # Append the error message to the logfile indicated
        try:
          f = open(self.logfilename,'a',errors='replace')
          f.write(self.getText(node[0]))
          f.close()
        except IOError as e:
          self.Error("Could not append log file %s\n" % self.logfilename)

    doc.unlink()

  def getResults(self):
    offset = 0
    status = self.neos.getJobStatus(self.jobNumber,self.password)
    try:
      while (status == "Waiting" or status=="Running"):
        (results,offset) = self.neos.getIntermediateResults(self.jobNumber, self.password,offset)
        if isinstance(results,xmlrpc.client.Binary):
          results = results.data.decode()
        if results and len(results):

          if self.logopt in [1,3,4]:
            # Send the output to the screen
            sys.stdout.write(results)
          if self.logopt in [2,4]:
            # Append the error message to the logfile indicated
            try:
              f = open(self.logfilename,'a')
              f.write(results)
              f.close()
            except IOError as e:
              self.Error("Could not append to log file %s" % self.logfilename)

          try:
            f = open(self.statfilename,'a')
            f.write("=1\n\n")
            f.write(results)
            f.write("=2\n")
            f.close()
          except IOError as e:
            self.Error("Could not append to status file %s\n" % self.statfilename)
        status = self.neos.getJobStatus(self.jobNumber,self.password)
        time.sleep(5)

    except KeyboardInterrupt as e:
      msg = '''Keyboard Interrupt\n\
Job is still running on remote machine\n\
To retrieve results, run GAMS using solver 'kestrel' with option file:\n\
kestrel_job %d\n\
kestrel_pass %s\n\n\
To stop job, run GAMS using solver 'kestrelkil' with above option file\n\
''' % (self.jobNumber, self.password)
      self.Error(msg)

    resultsXML = self.neos.getFinalResults(self.jobNumber,self.password)
    if isinstance(resultsXML,xmlrpc.client.Binary):
      resultsXML = resultsXML.data
    self.parseSolution(resultsXML)

if __name__=="__main__":
  #  print 'in gmske_ux.out'
  # Initialization phase

  try:
    kestrel = KestrelGamsClient(sys.argv)
    kestrel.parseControlFile()
    try:
      f = open(os.path.join(pathlib.Path(__file__).parent.absolute(),'gamsstmp.txt'),'r')
      auditLine = f.readline()
      f.close()
      kestrel.writeLog('NEOS Kestrel  ' + auditLine)
    except:
      pass
    kestrel.writeLog('\nFor terms of use please inspect https://neos-server.org/neos/termofuse.html\n\n')
    kestrel.writeErrorOutputFiles()
    kestrel.parseOptionsFile()
    kestrel.connectServer()
    kestrel.obtainSolvers()
  except KestrelException as e:
    kestrel.Error(e.msg)

  if kestrel.action=="solve":
    # Solve with job number and password retrieves the results
    # Otherwise we obtain them from the submission

    try:
      kestrel.parseOptionsFile()
      kestrel.writeLog("NEOS Solver: %s\n" % kestrel.solverName)
      if (not kestrel.jobNumber) or (not kestrel.password):
        kestrel.checkOptionsFile()
        kestrel.formSubmission()
        kestrel.submit()
      kestrel.getResults()
    except KestrelException as e:
      kestrel.Error(e.msg)

  elif kestrel.action=="submit":
    try:
      kestrel.parseOptionsFile()
      kestrel.checkOptionsFile()
      kestrel.formSubmission()
      kestrel.submit()

      fname = os.path.join(kestrel.scrdir, "kestrel." + kestrel.scrext)
      try:
        f = open(fname,'a')
        f.write("%d %s\n" % (kestrel.jobNumber, kestrel.password))
        f.close()
      except IOError as e:
        kestrel.Error("Could not append to submission file %s\n" % fname)

    except KestrelException as e:
      kestrel.Error(e.msg)

  elif kestrel.action=="retrieve":
    fname = os.path.join(kestrel.scrdir, "kestrel." + kestrel.scrext)

    try:
      f = open(fname,'r')
    except IOError as e:
      kestrel.Error("Could not open submission file %s\n" % fname)

    m = re.match(r'(\d+) ([a-zA-Z]+)',f.readline())
    if m:
      kestrel.jobNumber = int(m.groups()[0])
      kestrel.password = m.groups()[1]
    rest = f.read()
    f.close()

    if kestrel.jobNumber and kestrel.password:
      try:
        kestrel.getResults()
      except KestrelException as e:
        kestrel.Error(e.msg)
    else:
      kestrel.Error( "Corrupt submission file %s\n" % fname)

    if (rest):
      try:
        f = open(fname,'w')
        f.write(rest);
        f.close()
      except IOError as e:
        kestrel.Error("Could not rewrite submission file %s\n" % fname)
    else:
      os.unlink(fname)

  elif kestrel.action=="kill":
    # Kill and job retrieval do not require a valid solver
    kestrel.parseOptionsFile()
    if kestrel.jobNumber and kestrel.password:
      response = kestrel.neos.killJob(kestrel.jobNumber,kestrel.password)

      if kestrel.logopt in [1,3,4]:
        # Send the output to the screen
        sys.stdout.write("\n%s\n\n" % response)
      elif (kestrel.logopt == 2):
        # Append the error message to the logfile indicated
        try:
          f = open(kestrel.logfilename,'a')
          f.write("\n%s\n\n" % response)
          f.close()
        except IOError as e:
          kestrel.Error("Could not append to log file %s" % kestrel.logfilename)

      try:
        f = open(kestrel.statfilename,'a')
        f.write("=1\n\n")
        f.write("%s\n\n" % response)
        f.write("=2\n")
        f.close()
      except IOError as e:
        kestrel.Error("Could not append to status file %s\n" % kestrel.statfilename)
    else:
      kestrel.Error( "No 'kestrel_job' and 'kestrel_pass' options found in %s\n\n" % kestrel.optfilename)
