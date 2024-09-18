from enum import IntEnum, Enum
import json
import logging
import binascii
from datetime import datetime
import struct
import math
import html
import time
import re
import string
import os
from threading import Thread
from argparse import ArgumentParser, ArgumentDefaultsHelpFormatter
from serial import Serial
import requests
import urllib3
urllib3.disable_warnings()

# pylint: disable=protected-access

DATE_FMT = '%y/%m/%d,%H:%M:%S%z'
PING_TIMEOUT = 200
DEVICES = {}


def parse_args():
    parser = ArgumentParser(description='SimBox', formatter_class=ArgumentDefaultsHelpFormatter)
    parser.add_argument('-v', dest='verbose', action='count', help='Set verbose level', default=0)
    parser.add_argument('--log-file', dest='logfile', type=str, help='Set the logfile path', default='/var/log/simbox.log')
    parser.add_argument('--read-all-sms', dest='readall', action='store_true', help='Read all sms and exit')
    return parser.parse_args()


class SMSMessageFormat(IntEnum):
    PDU = 0
    Text = 1


class SMSTextMode(IntEnum):
    Hide = 0
    Show = 1


class NetworkStatus(IntEnum):
    NotRegistered = 0
    RegisteredHome = 1
    Searching = 2
    Denied = 3
    Unknown = 4
    RegisteredRoaming = 5


class ModuleStatus(IntEnum):
    Ready = 0
    Unavailable = 1
    Ringing = 3
    Calling = 4


class ModuleSleepMode(IntEnum):
    Disable = 0
    Enable = 1


class ATResp(IntEnum):
    ErrorNoResponse = -1
    ErrorDifferentResponse = 0
    OK = 1


class SMSStatus(IntEnum):
    Unread = 0
    Read = 1
    Unsent = 2
    Sent = 3
    All = 4

    @classmethod
    def fromStat(cls, stat):
        if stat == 'REC UNREAD':
            return cls.Unread
        if stat == 'REC READ':
            return cls.Read
        if stat == 'STO UNSENT':
            return cls.Unsent
        if stat == 'STO SENT':
            return cls.Sent
        if stat == 'ALL':
            return cls.All

    @classmethod
    def toStat(cls, stat) -> str:
        if stat == cls.Unread:
            return "REC UNREAD"
        if stat == cls.Read:
            return "REC READ"
        if stat == cls.Unsent:
            return "STO UNSENT"
        if stat == cls.Sent:
            return "STO SENT"
        if stat == cls.All:
            return "ALL"


class SMSCharset(Enum):
    GSM = 'GSM'
    IRA = 'IRA'
    HEX = 'HEX'
    PCCP936 = 'PCCP936'
    UCS2 = 'UCS2'


class IncomeFormat(IntEnum):
    Unknown = 0
    Ring = 1
    Sms = 2


class M590e:
    def __init__(self, port, baudrate, logger=None):
        self._port = port
        self._baudrate = baudrate
        self._serial = Serial(self._port, self._baudrate)
        self._logger = logger if logger else logging.getLogger("root")
        self.message_pool = []
        self.last_caller = None
        # Configure module
        self.setEchoOff()
        self.setSleepMode(0)
        self.setAOHMode(1)
        self.enableMessageIndicationMode()
        self.setCurrentClock()
        self.saveConfig()

    def sendATCmdWaitResp(self, cmd: str, response: str, timeout=.5, interByteTimeout=.1, attempts=1, addCR=False) -> ATResp:
        """
        This function is designed to check for simple one line responses, e.g. 'OK'.
        """
        self._logger.debug("Send AT Command: %s", cmd)
        self._serial.timeout = timeout
        self._serial.inter_byte_timeout = interByteTimeout

        status = ATResp.ErrorNoResponse
        for i in range(attempts):
            bcmd = cmd.encode('utf-8') + b'\r'
            if addCR:
                bcmd += b'\n'

            self._logger.debug("Attempt %d, (%s)", i + 1, bcmd)
            # self._serial.write(cmd.encode('utf-8')+b'\r')
            self._serial.write(bcmd)
            self._serial.flush()

            lines = self.getLines()
            if len(lines) < 1:
                continue
            line = lines[-1]
            self._logger.debug("Last Line: %s", line)

            if len(line) == 0 or line.isspace():
                continue
            if line == response:
                return ATResp.OK
            return ATResp.ErrorDifferentResponse
        return status

    def sendATCmdWaitReturnResp(self, cmd: str, response: str, timeout=.9, interByteTimeout=.1) -> tuple:
        """
        This function is designed to return data and check for a final response, e.g. 'OK'
        """
        self._logger.debug("Send AT Command: %s", cmd)
        self._serial.timeout = timeout
        self._serial.inter_byte_timeout = interByteTimeout

        self._serial.write(cmd.encode('utf-8') + b'\r')
        self._serial.flush()

        lines = self.getLines()
        if len(lines) == 0:
            return (ATResp.ErrorNoResponse, (None, None))

        _response = lines.pop(-1)
        self._logger.debug("Response: %s", _response)
        if len(_response) == 0 or _response.isspace():
            return (ATResp.ErrorNoResponse, (None, None))
        if response == _response:
            return (ATResp.OK, lines)
        return (ATResp.ErrorDifferentResponse, (None, None))

    def getLines(self) -> list:
        lines = self._serial.readlines()
        for i, v in enumerate(lines):
            v = bytes(filter(lambda x: x in string.printable.encode(), v))
            try:
                lines[i] = v.decode('utf-8').strip()
            except UnicodeDecodeError:
                lines[i] = binascii.unhexlify(v).decode('utf-16-be').strip()
            except Exception:  # pylint: disable=broad-except
                self._logger.error('Encode error for string %s', v)

        lines = [ln for ln in lines if len(ln) and not ln.isspace()]
        if lines:
            self._logger.debug("Lines: %s", lines)
        return lines

    def chekcIncomes(self) -> tuple:
        lines = self.getLines()
        for x, line in enumerate(lines):
            # check if someone RING
            if line == 'RING' and lines[x + 1].startswith('+CLIP'):
                matched = re.match(r'\+CLIP: "(.+?)",(\d+)', lines[x + 1])
                if not matched:
                    self._logger.warning("Incoming phone doesn't recognized: %s", lines[x + 1])
                    continue
                data = '+' + matched.groups()[0] if matched.groups()[1] == '145' else matched.groups()[0]
                if data != self.last_caller:
                    self.last_caller = data
                    return (IncomeFormat.Ring, data)
            # Check if someone no ring
            elif line == 'NO CARRIER':
                self.last_caller = None
            elif line == '+PBREADY':
                self._logger.warning('The module has restarted')
            # check SMS
            elif '+CMTI' in line:
                _, msg_id = self.parseReply(line, '+CMTI: ', index=1)
                self.message_pool.append(datetime.today())
                return (IncomeFormat.Sms, msg_id)
        return (IncomeFormat.Unknown, None)

    def parseReply(self, data, beginning, divider=',', index=0):
        """
        Parse an AT response line by checking the reply starts with the expected prefix,
        splitting the reply into its parts by the specified divider and then return the
        element of the response specified by index.
        """
        self._logger.debug("Parse Reply: %s, %s, %s, %d", data, beginning, divider, index)
        if not data.startswith(beginning):
            return False, None
        data = data.replace(beginning, "")
        data = data.split(divider)
        try:
            return True, data[index]
        except IndexError:
            return False, None

    def getSingleResponse(self, cmd, response, beginning, divider=",", index=0, timeout=.9, interByteTimeout=.1):
        """
        Run a command, get a single line response and the parse using the
        specified parameters.
        """
        status, data = self.sendATCmdWaitReturnResp(cmd, response, timeout=timeout, interByteTimeout=interByteTimeout)
        if status != ATResp.OK:
            return None
        if len(data) != 1:
            return None
        ok, data = self.parseReply(data[0], beginning, divider, index)
        if not ok:
            return None
        return data

    def getModuleStatus(self) -> ModuleStatus:
        """
        Query the work status of the module
        """
        self._logger.debug("Get Module Work Status")
        status = self.getSingleResponse("AT+CPAS", "OK", "+CPAS: ")
        if status is None:
            return status
        return ModuleStatus(int(status))

    def setEchoOff(self):
        """
        Switch off command echoing to simply response parsing.
        """
        self._logger.debug("Set Echo Off")
        self.sendATCmdWaitResp("ATE0", "OK")
        status = self.sendATCmdWaitResp("ATE0", "OK")
        return status == ATResp.OK

    def setSleepMode(self, mode: int) -> bool:
        """
        Enable or disable the sleep mode
        0: not allow to enter into power save mode
        1: allow to enter into power save mode
        """
        self._logger.debug("Set Sleep Mode")
        status = self.sendATCmdWaitResp(f"AT+ENPWRSAVE={mode}", "OK")
        return status == ATResp.OK

    def setSMSCharset(self, charset) -> bool:
        """
        To set the format of the TE character set
        """
        self._logger.debug("Set SMS Charset")
        status = self.sendATCmdWaitResp(f'AT+CSCS="{charset.value}"', "OK")
        return status == ATResp.OK

    def getLastError(self):
        """
        Get readon for last error
        """
        self._logger.debug("Get Last Error")
        error = self.getSingleResponse("AT+CEER", "OK", "+CEER: ")
        return error

    def getVersion(self):
        """
        Get the module firmware version.
        """
        self._logger.debug("Get TA Revision Identification of Software Release")
        # revision = self.getSingleResponse("AT+GMR", "OK", "+GMR: ", index=1)
        status, revision = self.sendATCmdWaitReturnResp("AT+GMR", "OK")
        if status == ATResp.OK:
            return revision

    def getIMEI(self):
        """
        Get the IMEI number of the module
        """
        self._logger.debug("Get International Mobile Equipment Identity (IMEI)")
        # imei = self.getSingleResponse("AT+CGSN", "OK", "+CGSN: ")
        status, [imei] = self.sendATCmdWaitReturnResp("AT+CGSN", "OK")
        if status == ATResp.OK:
            return imei
        return None

    def getNetworkStatus(self):
        """
        Get the current network connection status.
        """
        self._logger.debug("Get Network Status")
        status = self.getSingleResponse("AT+CREG?", "OK", "+CREG: ", index=1)
        if status is None:
            return status
        return NetworkStatus(int(status))

    def setSMSMessageFormat(self, fmt) -> bool:
        """
        Set the SMS message format either as PDU or text.
        """
        status = self.sendATCmdWaitResp(f"AT+CMGF={fmt}", "OK")
        return status == ATResp.OK

    def setSMSTextMode(self, mode) -> bool:
        status = self.sendATCmdWaitResp(f"AT+CSDH={mode}", "OK")
        return status == ATResp.OK

    def getNumSMS(self) -> tuple[int, int]:
        """
        Get the number of SMS on SIM card
        """
        self._logger.debug("Get Number of SMS")
        if not self.setSMSMessageFormat(SMSMessageFormat.Text):
            self._logger.error("Failed to set SMS Message Format!")
            return None

        if not self.setSMSTextMode(SMSTextMode.Show):
            self._logger.error("Failed to set SMS Text Mode!")
            return None

        num = self.getSingleResponse('AT+CPMS?', "OK", "+CPMS: ", divider='"SM",', index=1)
        if num is None:
            return num
        n, t, *_ = num.split(',')
        return int(n), int(t)

    def readSMS(self, number: int) -> tuple:
        """
        Returns status, phone number, date/time and message in location specified by 'number'.
        """
        self._logger.debug("Read SMS: %d", number)
        if not self.setSMSMessageFormat(SMSMessageFormat.Text):
            self._logger.error("Failed to set SMS Message Format!")
            return (None, None, None, None, None, None, None)

        if not self.setSMSTextMode(SMSTextMode.Show):
            self._logger.error("Failed to set SMS Text Mode!")
            return (None, None, None, None, None, None, None)

        if not self.setSMSCharset(SMSCharset.UCS2):
            self._logger.error("Failed to set SMS Charset!")
            return (None, None, None, None, None, None, None)

        status, (params, msg) = self.sendATCmdWaitReturnResp(f"AT+CMGR={number}", "OK")
        if status != ATResp.OK or not params.startswith("+CMGR: "):
            return (None, None, None, None, None, None, None)

        # stat   : message status = "REC UNREAD", "REC READ", "STO UNSENT", "STO SENT", "ALL"
        # oa     : originating address
        # alpha  : string of "oa" or "da"
        # scts   : service center timestamp "YY/MM/DD,HH:MM:SS+ZZ"
        # tooa   : originating address type
        # fo     :
        # pid    : protocol ID
        # dcs    : data coding scheme
        # sca    :
        # tosca  :
        # length : length of the message body

        params = map(lambda x: int(x) if x.isdigit() else x, params[7:].replace('"', '').split(','))
        stat, address, _, service_center_date, service_center_time, _, TPDU_first_octet, _, _, _, _, _ = params
        scts = datetime.strptime(service_center_date + ',' + service_center_time + '00', DATE_FMT)
        xref, t, c, msg = self.decodeSms(msg, is_single=TPDU_first_octet == 4)
        return SMSStatus.fromStat(stat), address, scts, xref, t, c, msg

    def readAllSMS(self, status=SMSStatus.All) -> tuple:
        """
        Return:
         - Status
         - Timestamp
         - From Address
         - Text
        """
        self._logger.debug("Read All SMS")
        if not self.setSMSMessageFormat(SMSMessageFormat.Text):
            self._logger.error("Failed to set SMS Message Format!")
            return (None, None, None, None)

        if not self.setSMSTextMode(SMSTextMode.Show):
            self._logger.error("Failed to set SMS Text Mode!")
            return (None, None, None, None)

        status, msgs = self.sendATCmdWaitReturnResp(f'AT+CMGL="{SMSStatus.toStat(status)}"', "OK")
        if status != ATResp.OK or not msgs or not msgs[0].startswith("+CMGL: ") or len(msgs) % 2 != 0:
            return (None, None, None, None)

        formatted = {}
        # decode all
        for n in range(0, len(msgs), 2):
            params, msg = msgs[n:n + 2]
            params = map(lambda x: int(x) if x.isdigit() else x, params[7:].replace('"', '').split(','))
            index, stat, address, _, service_center_date, service_center_time, _, _ = params
            scts = datetime.strptime(service_center_date + ',' + service_center_time + '00', DATE_FMT)
            xref, t, c, msg = self.decodeSms(msg)
            xref = index if xref == 0 else xref
            if not formatted.get(xref):
                formatted[xref] = {
                    'From': address,
                    'Timestamp': scts,
                    'Text': {c: msg},
                    'TotalCount': t,
                    'Status': stat,
                }
            else:
                formatted[xref]['Text'].update({c: msg})
        # return yeld
        for n, val in formatted.items():
            msg = ''.join(map(lambda x: x[1], sorted(val['Text'].items())))
            yield (val['Status'], val['Timestamp'], val['From'], msg)

    def deleteSMS(self, index: int, delflag=0) -> bool:
        """
        Delete the SMS in location specified by 'index'.
        delflag - could be:
            0: Delete the SMS messages with the specified recording numbers.
            1: Delete all read SMS messages.
            2: Delete all read and sent SMS messages.
            3: Delete all read, sent, and unsent SMS messages.
            4: Delete all messages.
        """
        self._logger.debug("Delete SMS: %d", index)
        status = self.sendATCmdWaitResp(f"AT+CMGD={index:02d},{delflag}", "OK")
        return status == ATResp.OK

    def sendUSSD(self, ussd: str):
        """
        Send Unstructured Supplementary Service Data message
        """
        if not self.setSMSMessageFormat(SMSMessageFormat.PDU):
            self._logger.error("Failed to set SMS Message Format!")
            return None

        if not self.setSMSTextMode(SMSTextMode.Hide):
            self._logger.error("Failed to set SMS Text Mode!")
            return None

        if not self.setSMSCharset(SMSCharset.GSM):
            self._logger.error("Failed to set SMS Charset!")
            return None

        self._logger.debug("Send USSD: %s", ussd)
        # encoded_ussd = binascii.hexlify(ussd.encode('utf-16-be')).decode()
        encoded_ussd = ussd
        reply = self.getSingleResponse(f'AT+CUSD=1,"{encoded_ussd}",15', "OK", "+CUSD: ", index=1, timeout=10., interByteTimeout=1.2)
        if reply is not None:
            return binascii.unhexlify(reply[1:-1]).decode('utf-16-be')
        self._logger.debug("No USSD response!")

    def setUartSpeed(self, value: int) -> bool:
        """
        Send UART baudrate speed
        """
        self._logger.debug("Set tty speed: %d", value)
        status = self.sendATCmdWaitResp(f'AT+IPR={value}', 'OK')
        return status == ATResp.OK

    def setAOHMode(self, status: int) -> bool:
        """
        Set AOH mode: 1 - enable, 0 - disable
        """
        self._logger.debug("Set AOH Mode: %d", status)
        status = self.sendATCmdWaitResp(f'AT+CLIP={status}', 'OK')
        return status == ATResp.OK

    def enableMessageIndicationMode(self) -> bool:
        """
        This command is to set how to inform the user after receiving new message
        from the network.
        """
        self._logger.debug("Set message indication Format")
        mt = 1  # new message indication code mode is +CMTI: “MT”, <index>, the message content storaged and don't display directly.
        status = self.sendATCmdWaitResp(f'AT+CNMI=2,{mt},0,0,0', 'OK')
        return status == ATResp.OK

    def saveConfig(self) -> bool:
        """
        This command is to save current valid configuration in the specified file (one
        of the two storage documents)
        """
        self._logger.debug("Save te current configuration")
        status = self.sendATCmdWaitResp('AT&W', 'OK')
        return status == ATResp.OK

    def getSignalQuery(self):
        """
        To check the receiving signal strength indication (RSSI) and the bit error rate (BER) of the channel
        """
        self._logger.debug("Check the receiving signal strength")
        # signal = int(self.getSingleResponse('AT+CSQ', "OK", '+CSQ: '))
        status, data = self.sendATCmdWaitReturnResp('AT+CSQ', 'OK')
        if status == ATResp.OK:
            return data[0].strip('+CSQ: ')
        return status

    def decodeSms(self, msg, is_single=False) -> tuple:
        """
        Return msgID - the first 6 bytes and decoded message
        """
        if is_single:
            return 0, 1, 1, binascii.unhexlify(msg).decode('utf-16-be')
        if msg[:6] == '050003':
            xref, total, current = struct.unpack('>BBB', binascii.unhexlify(msg[6:12]))
            return xref, total, current, binascii.unhexlify(msg[12:]).decode('utf-16-be')
        return 0, 1, 1, binascii.unhexlify(msg).decode('utf-16-be')
        # self._logger.error('Could not parse this message %s', msg)
        # return 0, 0, 0, None

    def ping(self) -> bool:
        """Send ping command"""
        self._logger.debug("Send AT command for ping module status")
        status = self.sendATCmdWaitResp('AT', 'OK')
        return status == ATResp.OK

    def setCurrentClock(self) -> bool:
        '''
        This set command sets the real-time clock of the module.
        time format yy/MM/dd,hh:mm:ss
        '''
        ts = datetime.strftime(datetime.today(), DATE_FMT[:-2])
        status = self.sendATCmdWaitResp(f'AT+CCLK="{ts}"', 'OK')
        return status == ATResp.OK

    def writePhoneBookNumber(self, index: int, number: str, text: str) -> bool:
        '''This command is to write the information in phone book'''
        number = re.sub(r'[^\+\d]*', '', number)
        cmd = f'AT+CPBW={index},"{number}",145,"{text}"'
        status = self.sendATCmdWaitResp(cmd, 'OK')
        return ATResp.OK == status

    def readPhoneBookNumber(self, index: int):
        '''This command is to read the information in phone book'''
        cmd = f'AT+CPBR={index}'
        status, data = self.sendATCmdWaitReturnResp(cmd, "OK")
        if status == ATResp.OK:
            _, number, _, name = data[0][7:].split(',')
            return status, number[1:-1], name[1:-1]
        return status, None, None

    def phoneBookStorage(self, name: str = ''):
        '''
        This command is to choose or get phone book storage

        name: str - if empty then function return the current storage
                  - SM = SIM storage
                  - FD = Fixed storage
                  - LD = Last dial-out storage
                  - ON = Locate storage
        '''
        cmd = 'AT+CPBS'
        if not name:
            data = self.getSingleResponse(f'{cmd}?', 'OK', '+CPBS: ')
            return data[1:-1]
        status = self.sendATCmdWaitResp(f'{cmd}="{name}"', "OK")
        return status == ATResp.OK

    def saveCurrentNumber(self, number: str):
        '''Save sim-card number to memory'''
        self.phoneBookStorage("ON")
        self.writePhoneBookNumber(1, number, "self")
        self.phoneBookStorage("SM")

    def getCurrentNumber(self):
        '''This command it to find the information od phone book'''
        status, data = self.sendATCmdWaitReturnResp('AT+CNUM', 'OK')
        if ATResp.OK == status:
            if not data:
                return None
            _, number, ntype = data[0][7:].split(',')
            return number[1:-1] if ntype == 129 else '+' + number[1:-1]
        return status

    def makeDial(self, phone: str):
        '''GPRS dialup through the external protocol'''
        self.sendATCmdWaitResp(f'ATD{phone};', 'OK')
        time.sleep(6)
        status = self.sendATCmdWaitResp('ATH', 'OK')
        return status


class CharsetEncoder:
    def __init__(self, charset):
        self.encode = getattr(self, f'{charset.value.lower()}_encode')

    def ira_encode(self, data: str) -> str:
        output = bytes()
        for ch in data:
            col = ord(ch) % 16
            row = math.ceil(ord(ch) / 16)
            b = int(f'{col:b}{row:b}', 2)
            output += bytes([b])
        return binascii.hexlify(output).decode()

    def ucs2_encode(self, data: str) -> str:
        return binascii.hexlify(data.encode('utf-16-be')).decode()

    def hex_encode(self, data: str) -> str:
        return binascii.hexlify(data.encode()).decode()

    def gsm_encode(self, data: str) -> str:
        return data

    def pccp936_encode(self, data: str) -> str:
        return data


def sendTelegramMessage(device, title: str, body: str):
    with open('simbox.conf.json') as fd:
        conf = json.load(fd)
    TOKEN = conf['TOKEN']
    url = f'https://api.telegram.org/bot{TOKEN}/sendMessage'
    msg = f'<b>{DEVICES[device]}</b>\n'
    msg += f'{title}\n'
    msg += body
    params = {'chat_id': conf['chat_id'], 'parse_mode': 'HTML', 'text': msg}
    resp = requests.get(url, params=params)
    if resp.status_code != 200:
        logging.error(resp.text)


def prepareSms(ts, address: str, msg: str):
    data = 'From: <code>%s</code>\nTime: <code>%s</code>\nText: <code>%s</code>'
    return data % (address, datetime.strftime(ts, DATE_FMT), html.escape(msg))


for item in map(lambda x: f'/dev/{x}', filter(lambda x: 'simbox' in x, os.listdir('/dev'))):
    DEVICES[item] = item


def extractSms(sim: M590e):
    for _, ts, address, msg in sim.readAllSMS(SMSStatus.Unread):
        sendTelegramMessage(
            sim._port,
            title='You have a new message',
            body=prepareSms(ts, address, msg)
        )


def collector(sim: M590e, readall: bool = False) -> None:
    timer = datetime.today()
    if sim.getNetworkStatus() is NetworkStatus.RegisteredHome:
        if readall:
            extractSms(sim)
            return
        sim.deleteSMS(0, 1)  # delete readed sms
        while True:
            if (datetime.today() - timer).seconds >= PING_TIMEOUT:
                timer = datetime.today()
                if not sim.ping():
                    logging.error('Module is not responding')
                    sendTelegramMessage(sim._port, 'Error!', 'Module is not responding')
            if sim.message_pool:
                # check if last message was 30 sec ago
                delta = datetime.today() - max(sim.message_pool)
                if delta.seconds >= 30:
                    logging.info('It need to unload all incoming messages')
                    extractSms(sim)
                    sim.message_pool = []
                    sim.deleteSMS(0, 1)  # delete readed sms reset cache
            try:
                itype, data = sim.chekcIncomes()
                if itype == IncomeFormat.Ring:
                    logging.info('Some motherfucker: %s tried to call you!', data)
                    sendTelegramMessage(sim._port, 'Some motherfucker tried to call you!', data)
                elif itype == IncomeFormat.Sms:
                    logging.info('New SMS id: %s', data)
            except KeyboardInterrupt:
                return
    logging.error('Could not registered!')


def main():
    args = parse_args()
    logging.basicConfig(
        format='%(levelname)s [ %(asctime)s ] ( %(funcName)s ) => %(message)s',
        level=logging.ERROR - args.verbose * 10,
        filename=args.logfile, filemode='a+'
    )
    threads = []
    for device in DEVICES:
        logging.info('Start for %s', device)
        sim = M590e(device, 115200)
        DEVICES[device] = sim.getCurrentNumber()
        threads.append(Thread(target=collector, args=(sim, args.readall,)))
        threads[-1].start()
    logging.info('Started')

    for t in threads:
        t.join()


if __name__ == '__main__':
    main()
